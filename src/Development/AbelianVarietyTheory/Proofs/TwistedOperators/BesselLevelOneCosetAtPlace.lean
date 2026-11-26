module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeLeft
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPower

@[expose] public section

attribute [-instance] UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPointBesselStaircaseLatticeFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPointBesselStaircaseLatticeFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.StairFrame

open GlobalTheory.FinPl (SplitPt Frame)
open GlobalTheory.FinPl.FrameLat

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

def emb : D.host.E →+* k := p.pr.comp (incA D)

theorem emb_apply (x : D.host.E) : emb p x = p.pr (incA D x) := rfl

theorem pr_int {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem coord_int {S : HSp D} {L : Lat S} {n : Type} [Fintype n] (b' : Matrix n (Fin S.rank) k)
    (h : ∀ z ∈ L, ∀ j, (b' *ᵥ fun i => emb p (z i)) j ∈ 𝒪[k]) {Y : Fin S.rank → AE D} (hY : Y ∈ latV S L (· = p.v)) (j : n) :
    (b' *ᵥ fun i => p.pr (Y i)) j ∈ 𝒪[k] := by
  induction hY using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have ht : p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] :=
      pr_int p (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
    have e : (fun i => p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i))) =
        p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) • fun i => emb p (x i) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, emb_apply, ← map_mul]
      congr 1
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [e, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem ht (h x hx j)
  | zero =>
    have e : (fun i => p.pr ((0 : Fin S.rank → AE D) i)) = 0 := by funext i; simp
    rw [e, mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun i => p.pr ((x + y) i)) = (fun i => p.pr (x i)) + fun i => p.pr (y i) := by funext i; simp
    rw [e, mulVec_add]; exact add_mem hx hy
  | neg x _ hx =>
    have e : (fun i => p.pr ((-x) i)) = -fun i => p.pr (x i) := by funext i; simp
    rw [e, mulVec_neg]; exact neg_mem hx

theorem map_latV {A B : HSp D} {L : Lat A} {L' : Lat B} (M : Matrix (Fin B.rank) (Fin A.rank) D.host.E)
    (h : ∀ z ∈ L, M *ᵥ z ∈ L') {P : GlobalTheory.FinPl.Pl D → Prop} {Y : Fin A.rank → AE D} (hY : Y ∈ latV A L P) :
    M.map (incA D) *ᵥ Y ∈ latV B L' P := by
  induction hY using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, M *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, map_apply, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem sec_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (u : Fin n → k) :
    (fun i => p.sec ((M.map (emb p) *ᵥ u) i)) = M.map (incA D) *ᵥ fun j => p.sec (u j) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (incA D _), sec_mul_right, mul_comm, emb_apply]

theorem mem_pi_one {n : Type} {x : n → k} :
    x ∈ Submodule.pi Set.univ (fun _ : n => (1 : Submodule 𝒪[k] k)) ↔ ∀ i, x i ∈ 𝒪[k] := by
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem exists_basis {A : HSp D} {Λ : Lat A} (hΛ : IsSelfDualC A Λ) : ∃ g : GL (Fin A.rank) k,
    ∀ x : Fin A.rank → k, (∀ i, x i ∈ 𝒪[k]) ↔ (fun i => p.sec ((g.val *ᵥ x) i)) ∈ latV A Λ (· = p.v) := by
  obtain ⟨β, hβ⟩ := ((GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p).1 A (Fin A.rank) 1 1 (by simp) (by simp)
  obtain ⟨Λ', h1, h2, -⟩ := exists_lat D k p A (Fin A.rank) β Λ hΛ
  letI : Λ'.IsLattice k := h1
  letI : Λ'.IsFullLattice k := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨m, s, c, hs, hc, -⟩ := exists_gen (p := p) hΛ
    have hexp := hc (β.b *ᵥ x)
    have hexp' := congrArg (β.b' *ᵥ ·) hexp
    simp only [mulVec_sum, mulVec_smul, mulVec_mulVec, β.b'b, one_mulVec] at hexp'
    rw [hexp']
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    apply Submodule.subset_span
    apply (h2 _).2
    simpa [mulVec_mulVec, β.bb', one_mulVec] using (sec_inc_mem (p := p) (hs l))
  obtain ⟨g, hg⟩ := GlobalTheory.LatPair.Det.exists_smul_stdLat_eq Λ'
  refine ⟨g, fun x => ?_⟩
  have h3 := h2 (g • x)
  rw [hβ, one_mulVec, ← hg, GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul, GlobalTheory.LatPair.mem_stdLat] at h3
  exact h3

theorem gram_star' (B : HSp D) (i j : Fin B.rank) : star (B.gram i j) = B.gram j i := by
  have := B.herm.eq (B.frame i) (B.frame j)
  simpa [HSpace.gram, starRingEnd_apply] using this

theorem perp_left {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram * frameMat B A d.ι = 0 := by
  refine Matrix.ext fun r i => ?_
  have e := congrArg star (congrFun (congrFun d.perp i) r)
  have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, Matrix.zero_apply, star_sum, star_mul',
    Finset.sum_mul, hsig, star_star, gram_star', star_zero] at e ⊢
  rw [← e, Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 1000000 in
theorem exists_frame {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Lat A}
    (hΛ : IsSelfDualC A Λ) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (s : Fin c → k) (hs : ∀ q, s q ≠ 0)
    (h1 : ∀ q, ∀ u ∈ 𝔟 q, (s q)⁻¹ * emb p u ∈ 𝒪[k]) (h2 : ∀ q, ∃ u ∈ 𝔟 q, ∃ o ∈ 𝒪[k], s q = o * emb p u) :
    ∃ (β : Frame p B (Fin B.rank)) (κ : Fin c → Fin B.rank),
      β.IsLat (d.lat Λ 𝔟) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧ Function.Injective κ ∧
      (∀ r i, β.b i (κ r) = s r * p.pr (incA D (d.a i r))) ∧
      ∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram).map
        (fun c => p.pr (incA D c)) * β.b) r j = 0 := by
  classical
  let σ : Fin A.rank ⊕ Fin c ≃ Fin B.rank := finSumFinEquiv.trans (finCongr d.rank)
  obtain ⟨g, hg⟩ := exists_basis p hΛ
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin B.rank) (Fin A.rank ⊕ Fin c) D.host.E, C = Matrix.fromCols (frameMat B A d.ι) d.a :=
    ⟨_, rfl⟩
  have hCr : IsUnit (C.submatrix id σ.symm) := by
    rw [← mulVec_injective_iff_isUnit]
    intro v v' h
    have h0 : C.submatrix id σ.symm *ᵥ (v - v') = 0 := by rw [mulVec_sub, h, sub_self]
    rw [submatrix_mulVec_equiv, hC, fromCols_mulVec] at h0
    obtain ⟨e1, e2⟩ := auxiliaryVectorDecomposition_eq_zero hε d _ _ h0
    refine sub_eq_zero.1 (funext fun i => ?_)
    obtain ⟨t, rfl⟩ := σ.surjective i
    rcases t with l | q
    · exact congrFun e1 l
    · exact congrFun e2 q
  let F' := (frameMat B A d.ι).map (emb p)
  let a' := d.a.map (emb p)
  let b₀ : Matrix (Fin B.rank) (Fin A.rank ⊕ Fin c) k := fromCols (F' * g.val) (a' * diagonal s)
  let b : Matrix (Fin B.rank) (Fin B.rank) k := b₀.submatrix id σ.symm
  have hb : IsUnit b := by
    have e : b = (C.submatrix id σ.symm).map (emb p) * (fromBlocks g.val 0 0 (diagonal s)).submatrix σ.symm σ.symm := by
      rw [← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, hC, fromCols_map, fromCols_mul_fromBlocks]
      simp only [Matrix.mul_zero, add_zero, zero_add]
      rfl
    rw [e]
    refine (hCr.map (emb p).mapMatrix).mul ?_
    rw [Matrix.isUnit_iff_isUnit_det, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_diagonal]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).mul (Finset.prod_ne_zero_iff.2 fun q _ => hs q).isUnit
  obtain ⟨U, hU⟩ := hb
  obtain ⟨β, hβ⟩ := ((GlobalTheory.InhPt.exists_splitPt_frame_char D).2 k p).1 B (Fin B.rank) U.val (U⁻¹).val U.mul_inv U.inv_mul
  rw [hU] at hβ
  have hbv : ∀ x : Fin B.rank → k, β.b *ᵥ x =
      F' *ᵥ (g.val *ᵥ fun l => x (σ (Sum.inl l))) + a' *ᵥ fun q => s q * x (σ (Sum.inr q)) := fun x => by
    rw [hβ, submatrix_mulVec_equiv, fromCols_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    have : diagonal s *ᵥ ((x ∘ σ.symm.symm) ∘ Sum.inr) = fun q => s q * x (σ (Sum.inr q)) := by
      funext q; rw [mulVec_diagonal]; rfl
    rw [this]
    rfl
  refine ⟨β, fun q => σ (Sum.inr q), fun x => ?_, σ.injective.comp Sum.inr_injective, fun r i => ?_, fun j hj r => ?_⟩
  · rw [mem_pi_one]
    constructor
    · intro hx
      have e : (fun i => p.sec ((β.b *ᵥ x) i)) = (fun i => p.sec ((F' *ᵥ (g.val *ᵥ fun l => x (σ (Sum.inl l)))) i)) +
          ∑ q, fun i => p.sec (s q * x (σ (Sum.inr q))) * incA D (d.a i q) := by
        funext i
        rw [hbv, Pi.add_apply, map_add (f := _), Pi.add_apply, Finset.sum_apply]
        congr 1
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [mulVec, dotProduct, map_sum, a', map_apply]
        exact Finset.sum_congr rfl fun q _ => by rw [sec_mul_right, mul_comm, emb_apply]
      rw [e]
      refine add_mem ?_ (sum_mem fun q _ => ?_)
      · rw [sec_mulVec]
        refine map_latV _ (fun z hz => ?_) ((hg _).1 fun l => hx _)
        exact ⟨z, hz, 0, fun q => (𝔟 q).zero_mem, by simp⟩
      · obtain ⟨u, hu, o, ho, hso⟩ := h2 q
        have hz : (fun i => u * d.a i q) ∈ d.lat Λ 𝔟 := by
          refine ⟨0, Λ.zero_mem, Pi.single q u, fun q' => ?_, ?_⟩
          · by_cases hq : q' = q
            · subst hq; simpa using hu
            · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q').zero_mem
          · funext i
            simp [mulVec_single, mul_comm]
        have h3 := int_mul_mem (sec_mem_intAt p _ (mul_mem ho (hx (σ (Sum.inr q))))) hz
        convert h3 using 2 with i
        rw [sec_mul_right, sec_mul_right, hso, map_mul (incA D), map_mul p.pr, emb_apply]
        congr 1
        ring
    · intro hx j
      have h3 := coord_int p β.b' (L := d.lat Λ 𝔟) ?_ hx j
      · simp only [p.pr_sec] at h3
        change (β.b' *ᵥ (β.b *ᵥ x)) j ∈ _ at h3
        rwa [mulVec_mulVec, β.b'b, one_mulVec] at h3
      · rintro _ ⟨y, hy, u, hu, rfl⟩ j
        let x' : Fin B.rank → k :=
          Sum.elim ((g⁻¹).val *ᵥ fun l => emb p (y l)) (fun q => (s q)⁻¹ * emb p (u q)) ∘ σ.symm
        have e1 : g.val *ᵥ ((g⁻¹).val *ᵥ fun l => emb p (y l)) = fun l => emb p (y l) := by
          rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
        have e : (fun i => emb p ((frameMat B A d.ι *ᵥ y + d.a *ᵥ u) i)) = β.b *ᵥ x' := by
          rw [hbv]
          simp only [x', Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
            mul_inv_cancel_left₀ (hs _)]
          rw [e1]
          funext i
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Pi.add_apply, mulVec, dotProduct, map_add (f := _), map_sum, map_mul, F', a', map_apply]
        rw [e, mulVec_mulVec, β.b'b, one_mulVec]
        obtain ⟨t, rfl⟩ := σ.surjective j
        simp only [x', Function.comp_apply, Equiv.symm_apply_apply]
        rcases t with l | q
        · refine (hg ((g⁻¹).val *ᵥ fun l => emb p (y l))).2 ?_ l
          rw [e1]
          exact sec_inc_mem hy
        · exact h1 q _ (hu q)
  · rw [hβ]
    simp only [b, b₀, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, mul_diagonal, a', map_apply]
    rw [mul_comm, emb_apply]
  · obtain ⟨t, rfl⟩ := σ.surjective j
    rcases t with l | q
    · have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram).map (emb p) * (F' * g.val) = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.map_mul, perp_left, Matrix.map_zero _ (map_zero _), Matrix.zero_mul]
      have e2 := congrFun (congrFun e r) l
      rw [hβ]
      simp only [Matrix.mul_apply (M := Matrix.map _ _), b, b₀, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl] at e2 ⊢
      exact e2
    · exact absurd ⟨q, rfl⟩ hj

end Local

section Ideal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
  {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem emb_int (x : 𝓞 D.host.E) : emb p (x : D.host.E) ∈ 𝒪[k] :=
  pr_int p (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, rfl⟩)

theorem emb_int_of_valuation (he : Formalism.L2.NTheta.IsIdemAt p.e w) {x : D.host.E} (hx : w.valuation D.host.E x ≤ 1) :
    emb p x ∈ 𝒪[k] := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer _ hx
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h0 => d.2 (by rw [h0]; exact zero_mem _)
  have hd : emb p ((d : 𝓞 D.host.E) : D.host.E)⁻¹ ∈ 𝒪[k] := by
    rw [p.int_iff, emb_apply, p.sec_pr]
    by_contra hc
    exact d.2 ((he.2 d hd0).2 hc)
  have h' : x * ((d : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := h
  have hd0' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h0 => hd0 (Subtype.ext h0)
  have e : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹ := by rw [← h', mul_inv_cancel_right₀ hd0']
  rw [e, map_mul]
  exact mul_mem (emb_int p n) hd

theorem exists_mem_valuation {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ∃ u ∈ I, w.valuation K u = WithZero.exp (-FractionalIdeal.count K w I) := by
  by_contra hc
  push Not at hc
  have hw : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  have hne : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * I ≠ 0 := mul_ne_zero hw hI
  have hle : I ≤ (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * I := by
    intro u hu
    refine (GroundTheory.Global.mem_fractionalIdeal_iff_forall_valuation_le (Units.mk0 _ hne) u).2 fun v => ?_
    have h1 := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal v hu
    rw [Units.val_mk0, FractionalIdeal.count_mul _ _ hw hI]
    by_cases hv : w = v
    · subst hv
      rw [FractionalIdeal.count_self]
      rcases eq_or_ne (w.valuation K u) 0 with h0 | h0
      · rw [h0]; exact zero_le
      · have h2 := lt_of_le_of_ne h1 (hc u hu)
        rw [← WithZero.exp_log h0, WithZero.exp_lt_exp] at h2
        rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
        omega
    · rwa [FractionalIdeal.count_maximal_coprime _ _ hv, zero_add]
  have := FractionalIdeal.count_mono K w hI hle
  rw [FractionalIdeal.count_mul _ _ hw hI, FractionalIdeal.count_self] at this
  omega

theorem gen_of_count (he : Formalism.L2.NTheta.IsIdemAt p.e w) {π : D.host.E}
    (hπ : w.valuation D.host.E π = WithZero.exp (-1)) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) {n : ℕ}
    (hn : FractionalIdeal.count D.host.E w I = n) :
    (∀ u ∈ I, (emb p π ^ n)⁻¹ * emb p u ∈ 𝒪[k]) ∧ ∃ u ∈ I, ∃ o ∈ 𝒪[k], emb p π ^ n = o * emb p u := by
  have hπn : w.valuation D.host.E (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  constructor
  · intro u hu
    rw [← map_pow, ← map_inv₀, ← map_mul]
    refine emb_int_of_valuation p he ?_
    have h1 := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal w hu
    rw [hn, ← hπn] at h1
    rw [map_mul, map_inv₀, ← div_eq_inv_mul]
    exact div_le_one_of_le₀ h1 zero_le
  · obtain ⟨u, hu, hv⟩ := exists_mem_valuation w hI
    rw [hn, ← hπn] at hv
    have hu0 : u ≠ 0 := fun h0 => by
      rw [h0, map_zero, hπn] at hv
      exact WithZero.exp_ne_zero hv.symm
    refine ⟨u, hu, emb p (π ^ n / u), emb_int_of_valuation p he ?_, ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ hv.ge zero_le
    · rw [← map_mul, div_mul_cancel₀ _ hu0, map_pow]

end Ideal

section Point

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke GlobalTheory.FinPl.SplitPoint
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_point {w : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) :
    ∃ (v : GlobalTheory.FinPl.Pl D) (p : SplitPt D (Fv D.host.F v)) (π : D.host.E) (ϖ : 𝒪[Fv D.host.F v]),
      p.v = w.under (𝓞 D.host.F) ∧ p.e = e ∧ w.valuation D.host.E π = WithZero.exp (-1) ∧
      (ϖ : Fv D.host.F v) = emb p π ∧ Irreducible ϖ := by
  obtain ⟨v, ε, hε, hs⟩ := he.1.2.2
  have hsa : SplitAt D v e := splitAt_of he.1 hε hs
  have hps : ∀ a, comp hsa (sec D v e a) = a := fun a => by
    rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]
  have hsp : ∀ x, sec D v e (comp hsa x) = e * x := fun x => (sc_spec hsa x).symm
  have hc := chart_comp hsa
  let p : SplitPt D (Fv D.host.F v) :=
    { v := v
      e := e
      split := he.1
      above := ⟨ε, hε, hs⟩
      pr := comp hsa
      sec := sec D v e
      pr_sec := hps
      sec_pr := hsp
      cont_pr := continuous_comp hsa
      cont_sec := continuous_sec
      int_iff := fun a => by
        have h1 := hc.2.2.2 (sec D v e a)
        rw [← hsp, hps] at h1
        rw [h1, isInt_Ov, mem_integer_iff] }
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have h1 : π ∈ w.asIdeal := by
    have := (w.intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; rfl)
    simpa using this
  have h2 : π ∉ w.asIdeal ^ 2 := fun h => by
    have := (w.intValuation_le_pow_iff_mem π 2).2 h
    rw [hπ, WithZero.exp_le_exp] at this
    omega
  obtain ⟨⟨q, hq, hirr⟩, -⟩ := GlobalTheory.SplitUnif.unif_chart e w v _ he hc π h1 h2
  have hO : 𝒪[Fv D.host.F v] = (v.adicCompletionIntegers D.host.F).toSubring :=
    Subring.ext fun a => mem_integer_iff _ v a
  let φ : 𝒪[Fv D.host.F v] ≃+* Ov D v := RingEquiv.subringCongr hO
  refine ⟨v, p, π, φ.symm q, ?_, rfl, ?_, hq, (MulEquiv.irreducible_iff φ.symm).2 hirr⟩
  · refine HeightOneSpectrum.ext (Ideal.ext fun t => ?_)
    change t ∈ v.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ w.asIdeal
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    have ht' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ≠ 0 := by simpa using ht
    have e1 : incA D (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E)⁻¹) =
        algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (t : D.host.F)⁻¹) := by
      rw [← IsScalarTower.algebraMap_apply,
        show (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E)⁻¹) =
          algebraMap D.host.F D.host.E (t : D.host.F)⁻¹ by rw [map_inv₀]; rfl]
      exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes _
    rw [he.2 _ ht', hc.2.2.2, isInt_Ov, e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    have e2 : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (t : D.host.F)⁻¹) =
        v.valuation D.host.F (t : D.host.F)⁻¹ := v.valuedAdicCompletion_eq_valuation' _
    have h0 : v.valuation D.host.F (t : D.host.F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact fun h => ht (Subtype.ext h)
    rw [e2, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0), ← v.valuation_lt_one_iff_mem (K := D.host.F)]
  · rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap w π

end Point

section Grid

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem count_stair (hq : OffQ D) {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) (c : ℕ)
    (q : Fin c) : stairId (G.pl.stA sc) (G.pl.stAbar sc) c q ≠ 0 ∧
      FractionalIdeal.count D.host.E (G.pl.w v) (stairId (G.pl.stA sc) (G.pl.stAbar sc) c q) =
        ((G.pl.depth sc v * (q.1 + 1) : ℕ) : ℤ) := by
  classical
  have hW : G.pl.w v ∈ G.pl.W0 := by
    unfold Places.W0
    convert Finset.mem_image_of_mem G.pl.w hv
  have hw : G.pl.w v ∈ locPl G μ₀ := (GlobalTheory.FunObj.GivenAdm.mem_locPl).2 (Or.inl hW)
  have hb := Good.badInt_notMem hL (G := G) (t := μ₀) hq (fun P hP => absurd
    (show (L.xiH μ₀).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ₀ P).2 (Or.inl hP))) hw
  have hA := count_AA_AAbar _ hb
  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  refine ⟨mul_ne_zero (pow_ne_zero _ h2.1) (inv_ne_zero (pow_ne_zero _ (ne_zero_of_conj h2.1 h2.2))), ?_⟩
  rw [count_stairId h2.1 (ne_zero_of_conj h2.1 h2.2), Places.stA, Places.stAbar,
    FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ (ne_zero_of_conj h1.1 h1.2)
      (inv_ne_zero hmo), FractionalIdeal.count_inv, FractionalIdeal.count_inv, count_modulBar G hw, count_modul, hA.1, hA.2,
    cosExp, if_pos hW, G.pl.under_w hv]
  push_cast
  ring

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_frame_col (hq : OffQ D) {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i : ℕ) (h : 1 ≤ i) (h' : i ≤ D.R.m)
    {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) :
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
      (p : SplitPt D k) (β : Frame p (G.V (.grid i 0)) (Fin (G.V (.grid i 0)).rank)) (ϖ : 𝒪[k])
      (κ : Fin (i - 1) → Fin (G.V (.grid i 0)).rank),
      p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
      β.IsLat (G.Λ (.grid i 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
      Irreducible ϖ ∧ Function.Injective κ ∧
      (∀ r j, β.b j (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec i h h').a j r))) ∧
      ∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec i h h').a *
        (G.V (.grid i 0)).gram).map (fun c => p.pr (incA D c)) * β.b) r j = 0 := by
  obtain ⟨e, he⟩ := G.pl.w_split v hv
  obtain ⟨v', p, π, ϖ, hpv, hpe, hπ, hϖ, hirr⟩ := exists_point he
  rw [G.pl.under_w hv] at hpv
  rw [← hpe] at he
  have hg := fun q : Fin (i - 1) =>
    gen_of_count p he hπ (count_stair hq hL G hv (i - 1) q).1 (count_stair hq hL G hv (i - 1) q).2
  have hϖ0 : emb p π ≠ 0 := by
    rw [← hϖ]
    exact fun h0 => hirr.ne_zero (Subtype.ext h0)
  obtain ⟨β, κ, b1, b2, b3, b4⟩ := exists_frame p (G.colDec i h h') (neg_ne_zero.2 one_ne_zero) (G.sp.P_is i h').sd
    (stairId (G.pl.stA sc) (G.pl.stAbar sc) (i - 1)) (fun q => emb p π ^ (G.pl.depth sc v * (q.1 + 1)))
    (fun q => pow_ne_zero _ hϖ0) (fun q => (hg q).1) (fun q => (hg q).2)
  have hlat : G.Λ (.grid i 0) = (G.colDec i h h').lat (G.sp.P i).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (i - 1)) :=
    G.sp.colLat i h h'
  refine ⟨_, _, _, _, _, p, β, ϖ, κ, hpv, he, by rw [hlat]; exact b1, hirr, b2, fun r j => ?_, b4⟩
  rw [hϖ]
  exact b3 r j

end Grid

theorem frame_shape : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v ∧
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Irreducible ϖ ∧
  Function.Injective κ ∧
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) ∧
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) := by
  intro D hq T L μ₀ hL sc G W M _ F _ σ h v hv
  exact exists_frame_col hq hL G (2 * (σ + 1) + 1) (by omega) (by omega) hv

end GlobalTheory.StairFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPointBesselStaircaseLatticeFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPoint_besselStaircaseLattice_frame : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v ∧
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Irreducible ϖ ∧
  Function.Injective κ ∧
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) ∧
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) := by
  first | exact @GlobalTheory.StairFrame.frame_shape | exact GlobalTheory.StairFrame.frame_shape | (intros; apply GlobalTheory.StairFrame.frame_shape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.FrameZero

theorem vecMul_row {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (q : Fin c) (m : ι) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = ((Formalism.UG.cT σ a * g).map φ * b) q m := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private theorem mulVec_col_eq_single_of_mul_eq_one {k m n : Type} [Field k] [Fintype m] [DecidableEq n] (b : Matrix m n k)
    (b' : Matrix n m k) (hb : b' * b = 1) (j : n) : (b' *ᵥ fun i => b i j) = Pi.single j 1 := by
  funext i
  show ∑ l, b' i l * b l j = _
  rw [← Matrix.mul_apply, hb, Matrix.one_apply, Pi.single_apply]
private theorem cA_incA_eq_incA_sig (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := rfl
end GlobalTheory.FrameZero

theorem GlobalTheory.FrameZero.xclauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  unfold GlobalTheory.AscFin.OnStd All
  intro D _ T L μ0 _ sc G _ M _ F hF σ h v _ k _ _ _ _ p β ϖ κ _ _ _ hirr hinj hb hperp
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hϖ : (ϖ : k) ≠ 0 := fun h0 => hirr.ne_zero (Subtype.ext h0)
  have hx0 : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero)
  have hx1 : p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr ((map_ne_zero _).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero))
  have hx : ∀ i (q : Fin (σ + 1)), xZero (F.dJ (σ + 1) h) i q = incA D ((-D.host.xi0) ^ (q.1 + 1) *
      (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩) := by
    intro i q
    show incA D ((F.dJ (σ + 1) h).e i q) = _
    rw [he]
    rfl
  refine ⟨fun q => (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) *
      ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹)⁻¹,
    fun q => (p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) *
      (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)))⁻¹, ?_, ?_⟩
  · intro q
    have hcol : (fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹) •
          fun i => β.b i (κ ⟨q.1, by omega⟩) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb, hx, map_mul, map_mul, map_pow, map_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ)]
    dsimp only
    rw [hcol, Matrix.mulVec_smul, mulVec_col_eq_single_of_mul_eq_one _ _ β.b'b, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx0) (inv_ne_zero (pow_ne_zero _ hϖ))), one_smul]
  · intro q
    have hrow : (fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) =
        p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) •
          fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
            ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩)) := by
      funext i
      rw [hx, cA_incA_eq_incA_sig]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, RingHom.comp_apply]
    have key : ∀ r : Fin (2 * (σ + 1) + 1 - 1), ∑ j, p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram)
            ⟨q.1, by omega⟩ j)) * ((ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) *
          p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j r))) =
        (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram *
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a) ⟨q.1, by omega⟩ r)) := by
      intro r
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul]
      ring
    have hN : ((fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
          ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩))) ᵥ*
          ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) =
        (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)) •
          Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1 := by
      funext m
      refine (GlobalTheory.FrameZero.vecMul_row (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
        (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a (G.V (.grid (2 * (σ + 1) + 1) 0)).gram β.b
        ⟨q.1, by omega⟩ m).trans ?_
      by_cases hm : m ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hm
        rw [Matrix.mul_apply]
        simp only [hb, Matrix.map_apply, RingHom.comp_apply]
        rw [key, (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).gram, antiDiagonalSignGramMatrix]
        split_ifs with h1 h3
        · exfalso
          have h4 := congrArg Fin.val h3
          simp only at h1 h4
          omega
        · have hrv : r.1 = 2 * (σ + 1) - 1 - q.1 := by simp only at h1; omega
          rw [map_one, map_one, mul_one, Pi.smul_apply, Pi.single_apply,
            if_pos (congrArg κ (Fin.ext hrv)), smul_eq_mul, mul_one, hrv]
        · rw [map_zero, map_zero, mul_zero, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
          intro hk
          have h4 := congrArg Fin.val (hinj hk)
          simp only at h1 h4
          omega
      · rw [Pi.smul_apply, Pi.single_apply, if_neg (fun e => hm ⟨_, e.symm⟩), smul_zero]
        exact hperp m hm _
    dsimp only
    rw [hrow, Matrix.smul_vecMul, hN, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx1) (pow_ne_zero _ hϖ)), one_smul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_basePoint_scaled_coordinates : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  first | exact @GlobalTheory.FrameZero.xclauses | exact GlobalTheory.FrameZero.xclauses | (intros; apply GlobalTheory.FrameZero.xclauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.AscFin.FrameBF

theorem frame_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b ≠ ι a) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h v hv
  obtain ⟨k, i1, i2, i3, i4, p, β, ϖ, κ, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.exists_splitPoint_besselStaircaseLattice_frame D hq T L μ0 hL sc G W M hM F hF σ h v hv
  obtain ⟨s, t, hs, ht⟩ := GlobalTheory.T.besselStep_basePoint_scaled_coordinates D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7
  refine ⟨k, i1, i2, i3, i4, p, β, fun q => κ ⟨q.1, by omega⟩, fun q => κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩, s, t,
    h1, h2, h3, ?_, ?_, ?_, hs, ht, fun a ha =>
      ⟨GlobalTheory.T.split_frame_odd_lattice_left D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7 s hs a ha,
       GlobalTheory.T.split_frame_odd_lattice_right D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7 t ht a ha⟩⟩
  · intro a b e
    exact Fin.ext (Fin.mk.inj (h5 e))
  · intro a b e
    have := Fin.mk.inj (h5 e)
    have ha := a.2; have hb := b.2
    exact Fin.ext (by omega)
  · intro a b e
    have := Fin.mk.inj (h5 e)
    have ha := a.2; have hb := b.2
    omega

end GlobalTheory.AscFin.FrameBF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_frame_odd_level : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b ≠ ι a) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  first | exact @GlobalTheory.AscFin.FrameBF.frame_bf | exact GlobalTheory.AscFin.FrameBF.frame_bf | (intros; apply GlobalTheory.AscFin.FrameBF.frame_bf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetBF

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), ∀ (u : UX D ρ), ∀ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a) → ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) k ⬝ xZero (F.dJ ρ h) - mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h v hv g hg u a ha hoff
  cases ρ with
  | zero =>
    exact ⟨1, one_mem _, one_mem _, fun i j => j.elim0⟩
  | succ σ =>
    obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hdisj, hX, hΦ, hA⟩ :=
      GlobalTheory.T.split_local_frame_odd_level D hQ T L μ0 hL sc G W M hM F hF σ h v hv
    obtain ⟨ha1, ha2⟩ := hA a ha
    subst hpv
    obtain ⟨k₀, hk₀, hoff'⟩ := GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power D k p _ σ β (xZero (F.dJ (σ + 1) h)) ι ι' s t (G.pl.depth sc p.v)
      (G.pl.depth_pos sc _) hι hι' (fun a b hab => absurd hab (hdisj a b)) hX hΦ g hg u a ha1 ha2 hoff
    have hsd : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
      (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
    refine ⟨β.gl _, GlobalTheory.T.framedCongruenceElement_mem_principalCongruence D hQ T L μ0 hL sc G W M hM (.grid (2 * (σ + 1) + 1) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
    exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetBF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_orbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), ∀ (u : UX D ρ), ∀ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a) → ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) k ⬝ xZero (F.dJ ρ h) - mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1)) := by
  first | exact @GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate | exact GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate | (intros; apply GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.OneCosetBFPlace

theorem one_coset_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  intro D hq T L μ hL sc G W M hM F hF ρ h v hv g hg hc
  obtain ⟨u, a, ha, hc⟩ := hc
  obtain ⟨k, hk, hkv, hm⟩ := GlobalTheory.T.besselStep_orbit_at_badPlace_eq_congruenceTranslate D hq T L μ hL sc G W M hM F hF ρ h v hv g hg u a ha hc
  obtain ⟨r, hr, hrv, rfl⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ _ _ g k u hg hkv hm
  exact ⟨r, hr, hrv, k⁻¹, inv_mem hk, inv_mem hkv, rfl⟩

end GlobalTheory.OneCosetBFPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevel_one_coset_at_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  first | exact @GlobalTheory.OneCosetBFPlace.one_coset_place | exact GlobalTheory.OneCosetBFPlace.one_coset_place | (intros; apply GlobalTheory.OneCosetBFPlace.one_coset_place <;> assumption)
end

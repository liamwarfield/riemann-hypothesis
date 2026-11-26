module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisPhi
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem lvBasis_φ_act (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    actVB PD ρ g (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V) (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.actVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lvBasis_φ_mul (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := V) x) =
      φVB PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.mulVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lvBasis_mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.Dcris, sub_eq_zero]

theorem lvBasis_mem_DcrisL (ρ : Representation LL G V) (τ₀ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ₀ ↔ x ∈ Dcris PD ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ₀ c • x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.DcrisL, sub_eq_zero]

theorem lvBasis_φ_Dcris (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [lvBasis_mem_Dcris] at hx ⊢
  intro g
  rw [lvBasis_φ_act, hx g]

theorem lvBasis_φ_letter (ρ : Representation LL G V) {τ₀ τ₁ : K₀ →ₐ[Qp] LL}
    (h : τ₁.comp PD.σ = τ₀) {x : V ⊗[Qp] B} (hx : x ∈ DcrisL PD ρ τ₀) :
    φVB PD (LL := LL) (V := V) x ∈ DcrisL PD ρ τ₁ := by
  rw [lvBasis_mem_DcrisL] at hx ⊢
  refine ⟨lvBasis_φ_Dcris PD ρ hx.1, fun c => ?_⟩
  obtain ⟨c', rfl⟩ := PD.σ_bij.2 c
  rw [lvBasis_φ_mul, hx.2 c', map_smul, ← h, AlgHom.comp_apply]

theorem lvBasis_φ_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have hfun : ⇑(Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := V)) = ⇑(LinearMap.lTensor V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.φVB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [hfun]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj

theorem lvBasis_φpow_inj (k : ℕ) : Function.Injective ((φVB PD (LL := LL) (V := V)) ^ k) := by
  first
  | (rw [Module.End.coe_pow]; exact (lvBasis_φ_inj PD).iterate k)
  | simpa using (lvBasis_φ_inj PD).iterate k

private theorem eigen_finset_eq_zero_of_injective_embeddings {ι : Type} [DecidableEq ι] (τ : ι → (K₀ →ₐ[Qp] LL))
    (hτ : Function.Injective τ) (s : Finset ι) : ∀ (x : ι → V ⊗[Qp] B),
    (∀ i ∈ s, ∀ c, Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i) →
    ∑ i ∈ s, x i = 0 → ∀ i ∈ s, x i = 0 := by
  induction s using Finset.induction_on with
  | empty => intro x _ _ i hi; simp at hi
  | @insert j s hj ih =>
    intro x hx hs
    rw [Finset.sum_insert hj] at hs
    have h2 : ∑ i ∈ s, x i = -x j := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs
    have key : ∀ c, ∀ i ∈ s, (τ i c - τ j c) • x i = 0 := by
      intro c
      apply ih (fun i => (τ i c - τ j c) • x i)
      · intro i hi c'
        rw [map_smul, hx i (Finset.mem_insert_of_mem hi) c', smul_comm]
      · have h1 := congrArg (Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c) hs
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, map_zero, hx j (Finset.mem_insert_self j s) c,
          Finset.sum_congr rfl (fun i hi => hx i (Finset.mem_insert_of_mem hi) c)] at h1
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, ← Finset.smul_sum, h2, smul_neg, sub_neg_eq_add, add_comm]
        exact h1
    have hs0 : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have hij : τ i ≠ τ j := fun h => hj (by rw [← hτ h]; exact hi)
      obtain ⟨c, hc⟩ : ∃ c, τ i c ≠ τ j c := by
        by_contra hne
        push_neg at hne
        exact hij (AlgHom.ext hne)
      exact (smul_eq_zero.mp (key c i hi)).resolve_left (sub_ne_zero.mpr hc)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_eq_zero hs0, add_zero] at hs
      exact hs
    · exact hs0 i hi

theorem lvBasis_indep {ι : Type} [Fintype ι] (τ : ι → (K₀ →ₐ[Qp] LL)) (hτ : Function.Injective τ)
    (x : ι → V ⊗[Qp] B)
    (hx : ∀ i c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i)
    (hs : ∑ i, x i = 0) (i : ι) : x i = 0 := by
  classical
  exact eigen_finset_eq_zero_of_injective_embeddings τ hτ Finset.univ x (fun i _ c => hx i c) hs i (Finset.mem_univ i)

end Formalism.MainNotions.N.Ln03.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {T : LocLat G Qp LL O}

theorem lvBasis_cmp_congr {a b : W.DD T} (ha : a ∈ W.N T) (hb : b ∈ W.N T) (h : a = b) :
    W.cmp T ⟨a, ha⟩ = W.cmp T ⟨b, hb⟩ := by
  subst h
  rfl

theorem lvBasis_cmp_add {a b : W.DD T} (ha : a ∈ W.N T) (hb : b ∈ W.N T) (hab : a + b ∈ W.N T) :
    W.cmp T ⟨a + b, hab⟩ = W.cmp T ⟨a, ha⟩ + W.cmp T ⟨b, hb⟩ := by
  rw [← map_add (f := _)]
  rfl

theorem lvBasis_letE_idem (i : ZMod n) (x : W.DD T) :
    (letE i : LetA O n) • (letE i : LetA O n) • x = (letE i : LetA O n) • x := by
  rw [smul_smul, letE_mul_self]

theorem lvBasis_sum_letE : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem lvBasis_cmp_of_eq {w z y : W.DD T} (hw : w ∈ W.N T) (hz : z ∈ W.N T) (hy : y ∈ W.N T)
    (o : O) (h : y = o • w + (letπ : LetA O n) • z) :
    W.cmp T ⟨y, hy⟩ = algebraMap O LL o • W.cmp T ⟨w, hw⟩ := by
  have e : (⟨y, hy⟩ : ↥(W.N T)) = o • ⟨w, hw⟩ + (letπ : LetA O n) • ⟨z, hz⟩ := Subtype.ext h
  rw [e, map_add (f := _), W.cmp_smul, W.cmp_π, add_zero]

theorem lvBasis_cmp_smul_const {w : W.DD T} (hw : w ∈ W.N T) (a : LetA O n) (o : O)
    (ha : ∀ j, PowerSeries.constantCoeff (a j) = o) (h : a • w ∈ W.N T) :
    W.cmp T ⟨a • w, h⟩ = algebraMap O LL o • W.cmp T ⟨w, hw⟩ := by
  have hd : ∀ j, (PowerSeries.X : PowerSeries O) ∣ a j - PowerSeries.C o := fun j =>
    PowerSeries.X_dvd_iff.2 (by rw [map_sub, ha j, PowerSeries.constantCoeff_C, sub_self])
  choose b hb using hd
  have ea : a = o • (1 : LetA O n) + (letπ : LetA O n) * b := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, Pi.mul_apply, letπ]
    rw [PowerSeries.smul_eq_C_mul, mul_one, ← hb j]
    ring
  refine lvBasis_cmp_of_eq hw ((W.N T).smul_mem b hw) h o ?_
  rw [ea, add_smul, mul_smul, smul_assoc, one_smul]

theorem lvBasis_cmp_smul_letter {w : W.DD T} (hw : w ∈ W.N T) (i : ZMod n)
    (hwi : (letE i : LetA O n) • w = w) (a : LetA O n) (h : a • w ∈ W.N T) :
    W.cmp T ⟨a • w, h⟩ = algebraMap O LL (PowerSeries.constantCoeff (a i)) • W.cmp T ⟨w, hw⟩ := by
  obtain ⟨b, hb⟩ := PowerSeries.X_dvd_iff.2
    (by rw [map_sub, PowerSeries.constantCoeff_C, sub_self] :
      PowerSeries.constantCoeff (a i - PowerSeries.C (PowerSeries.constantCoeff (a i))) = 0)
  refine lvBasis_cmp_of_eq hw ((W.N T).smul_mem (Pi.single i b) hw) h _ ?_
  have ea : a * letE i = PowerSeries.constantCoeff (a i) • (letE i : LetA O n) + letπ * Pi.single i b := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, letE, letπ, Pi.single_eq_same,
        PowerSeries.smul_eq_C_mul, mul_one]
      rw [← hb]
      ring
    · simp [letE, letπ, hj]
  calc a • w = a • ((letE i : LetA O n) • w) := by rw [hwi]
    _ = (a * letE i) • w := by rw [mul_smul]
    _ = _ := by rw [ea, add_smul, smul_assoc, hwi, mul_smul]

theorem lvBasis_q₀_const : PowerSeries.constantCoeff W.q₀ = (PD.p : O) := by
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * W.q₀) = PowerSeries.constantCoeff W.q₀ := by
    simp
  rw [← h1, W.q₀_def]
  have e : (1 + PowerSeries.X : PowerSeries O) ^ PD.p - 1 =
      (((1 + Polynomial.X) ^ PD.p - 1 : Polynomial O) : PowerSeries O) := by
    simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_X]
  rw [e, Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow,
    Polynomial.coeff_one]
  simp

theorem lvBasis_Q_const (j : ZMod n) : PowerSeries.constantCoeff (W.Q j) = (PD.p : O) := by
  have hφ : ∀ (a : LetA O n) (j : ZMod n),
      PowerSeries.constantCoeff (W.φA a j) = PowerSeries.constantCoeff (a (j - 1)) := by
    intro a j
    have e : W.φA a j = W.φ₀ (a (j - 1)) := rfl
    rw [e, constCoeff_algHom W.φ₀ (by rw [W.φ₀_X, map_mul, PowerSeries.constantCoeff_X, zero_mul])]
  have key : ∀ (k : ℕ) (j : ZMod n), PowerSeries.constantCoeff (((W.φA ^ k) W.q) j) = (PD.p : O) := by
    intro k
    induction k with
    | zero => intro j; exact lvBasis_q₀_const
    | succ k ih => intro j; rw [pow_succ', AlgHom.mul_apply, hφ, ih]
  exact key _ j

theorem lvBasis_cmp_Qpow {w : W.DD T} (hw : w ∈ W.N T) (k : ℕ) (h : W.Q ^ k • w ∈ W.N T) :
    W.cmp T ⟨W.Q ^ k • w, h⟩ = ((PD.p : ℕ) : LL) ^ k • W.cmp T ⟨w, hw⟩ := by
  rw [lvBasis_cmp_smul_const hw _ (((PD.p : ℕ) : O) ^ k)
    (fun j => by rw [Pi.pow_apply, map_pow, lvBasis_Q_const]) h, map_pow, map_natCast]

theorem lvBasis_p_ne_zero (W : LocWach PD LL O v n) : ((PD.p : ℕ) : LL) ≠ 0 := by
  intro h0
  have hv := W.v_l
  rw [h0, AddValuation.map_zero] at hv
  exact WithTop.top_ne_one hv

theorem lvBasis_letter_span (hspan : Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ)
    (j : ZMod n) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb j)) :
    d ∈ Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE j : LetA O n) • x)) := by
  classical
  have hd' : d ∈ Submodule.span LL (Set.range (W.cmp T)) := by
    rw [hspan]
    exact ((lvBasis_mem_DcrisL PD T.ρ _ d).1 hd).1
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hd'
  let z : ZMod n → T.V ⊗[Qp] B := fun i => f.sum fun x a => a • W.cmp T ((letE i : LetA O n) • x)
  have hzi : ∀ i, z i ∈ DcrisL PD T.ρ (W.emb i) := fun i =>
    Submodule.finsuppSum_mem _ _ _ _ fun x _ => Submodule.smul_mem _ _ (W.cmp_letter T i x)
  have hzj : z j ∈ Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE j : LetA O n) • x)) :=
    Submodule.finsuppSum_mem _ _ _ _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hzs : ∑ i, z i = f.sum fun x a => a • W.cmp T x := by
    simp only [z, Finsupp.sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, ← map_sum, ← Finset.sum_smul, lvBasis_sum_letE, one_smul]
  have key := lvBasis_indep W.emb W.emb_bij.1
    (fun i => z i - if i = j then (f.sum fun x a => a • W.cmp T x) else 0) (fun i c => by
      have h1 := ((lvBasis_mem_DcrisL PD T.ρ _ _).1 (hzi i)).2 c
      split_ifs with hij
      · subst hij
        rw [map_sub, smul_sub, h1, ((lvBasis_mem_DcrisL PD T.ρ _ _).1 hd).2 c]
      · rw [sub_zero, h1]) (by simp [Finset.sum_sub_distrib, hzs]) j
  rw [if_pos rfl, sub_eq_zero] at key
  rw [← key]
  exact hzj

theorem lvBasis_cmp_mem_φ (h3 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))
    (j : ZMod n) {y : W.DD T} (hy : y ∈ W.N T) (hyj : (letE j : LetA O n) • y = y) :
    W.cmp T ⟨y, hy⟩ ∈ (Dcris PD T.ρ).map (φVB PD (LL := LL) (V := T.V)) := by
  set U := (Dcris PD T.ρ).map (φVB PD (LL := LL) (V := T.V)) with hU
  have key : ∀ z ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
      ∃ m : ℕ, ∀ i, ∃ h : (letE i : LetA O n) • W.Q ^ m • z ∈ W.N T, W.cmp T ⟨_, h⟩ ∈ U := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨k, hk⟩ := W.N_φ T x hx
      have hk2 : W.Q ^ k • W.φD T x ∈ W.N T := hk
      refine ⟨k, fun i => ⟨(W.N T).smul_mem _ hk2, ?_⟩⟩
      have hx' : (letE (i - 1) : LetA O n) • x ∈ W.N T := (W.N T).smul_mem _ hx
      have he : (letE i : LetA O n) • W.Q ^ k • W.φD T x =
          W.Q ^ k • W.φD T ((letE (i - 1) : LetA O n) • x) := by
        rw [φD_smulA W, φA_letE W, smul_comm]
      have hk' : W.Q ^ k • W.φD T ((letE (i - 1) : LetA O n) • x) ∈ W.N T := he ▸ (W.N T).smul_mem _ hk2
      rw [lvBasis_cmp_congr _ hk' he]
      rw [h3 ⟨_, hx'⟩ k hk']
      exact U.smul_mem _ (Submodule.mem_map_of_mem (W.cmp_mem T _))
    | zero =>
      refine ⟨0, fun i => ⟨by simp, ?_⟩⟩
      rw [lvBasis_cmp_congr _ (W.N T).zero_mem (by simp)]
      have h0 : W.cmp T ⟨0, (W.N T).zero_mem⟩ = 0 := map_zero (W.cmp T)
      rw [h0]
      exact U.zero_mem
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, hm₁⟩ := h₁
      obtain ⟨m₂, hm₂⟩ := h₂
      refine ⟨m₁ + m₂, fun i => ?_⟩
      obtain ⟨ha, hca⟩ := hm₁ i
      obtain ⟨hb, hcb⟩ := hm₂ i
      have ha' := (W.N T).smul_mem (W.Q ^ m₂) ha
      have hb' := (W.N T).smul_mem (W.Q ^ m₁) hb
      have he : (letE i : LetA O n) • W.Q ^ (m₁ + m₂) • (z₁ + z₂) =
          W.Q ^ m₂ • (letE i : LetA O n) • W.Q ^ m₁ • z₁ +
            W.Q ^ m₁ • (letE i : LetA O n) • W.Q ^ m₂ • z₂ := by
        simp only [smul_add, smul_smul]
        congr 1 <;> congr 1 <;> ring
      refine ⟨he ▸ (W.N T).add_mem ha' hb', ?_⟩
      rw [lvBasis_cmp_congr _ ((W.N T).add_mem ha' hb') he, lvBasis_cmp_add ha' hb',
        lvBasis_cmp_Qpow ha, lvBasis_cmp_Qpow hb]
      exact U.add_mem (U.smul_mem _ hca) (U.smul_mem _ hcb)
    | smul a z _ hz =>
      obtain ⟨m, hm⟩ := hz
      refine ⟨m, fun i => ?_⟩
      obtain ⟨h, hc⟩ := hm i
      have he : (letE i : LetA O n) • W.Q ^ m • (a • z) = a • (letE i : LetA O n) • W.Q ^ m • z := by
        rw [smul_comm (W.Q ^ m) a z, smul_comm (letE i : LetA O n) a]
      refine ⟨he ▸ (W.N T).smul_mem a h, ?_⟩
      rw [lvBasis_cmp_congr _ ((W.N T).smul_mem a h) he,
        lvBasis_cmp_smul_letter h i (lvBasis_letE_idem i _)]
      exact U.smul_mem _ hc
  obtain ⟨k, hk⟩ := W.N_φinv T y hy
  have hk2 : W.Q ^ k • y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) := hk
  obtain ⟨m, hm⟩ := key _ hk2
  obtain ⟨h, hc⟩ := hm j
  have he : (letE j : LetA O n) • W.Q ^ m • W.Q ^ k • y = W.Q ^ (m + k) • y := by
    rw [smul_comm (letE j : LetA O n), smul_comm (letE j : LetA O n), hyj, pow_add, mul_smul]
  rw [lvBasis_cmp_congr _ ((W.N T).smul_mem _ hy) he, lvBasis_cmp_Qpow hy] at hc
  have hc2 := U.smul_mem (((PD.p : ℕ) : LL) ^ (m + k))⁻¹ hc
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (lvBasis_p_ne_zero W)), one_smul] at hc2

theorem lvBasis_letter_pre (hspan : Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ)
    (h3 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))
    (j : ZMod n) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb j)) :
    ∃ d' ∈ DcrisL PD T.ρ (W.emb (j - 1)), φVB PD (LL := LL) (V := T.V) d' = d := by
  have hdU : d ∈ (Dcris PD T.ρ).map (φVB PD (LL := LL) (V := T.V)) := by
    refine Submodule.span_le.2 ?_ (lvBasis_letter_span hspan j hd)
    rintro _ ⟨x, rfl⟩
    exact lvBasis_cmp_mem_φ h3 j ((W.N T).smul_mem _ x.2) (lvBasis_letE_idem j _)
  obtain ⟨d', hd'D, rfl⟩ := hdU
  refine ⟨d', (lvBasis_mem_DcrisL PD T.ρ _ d').2 ⟨hd'D, fun c => ?_⟩, rfl⟩
  apply lvBasis_φ_inj PD (LL := LL) (V := T.V)
  rw [← lvBasis_φ_mul, ((lvBasis_mem_DcrisL PD T.ρ _ _).1 hd).2, map_smul]
  congr 1
  rw [← W.emb_σ (j - 1), AlgHom.comp_apply, sub_add_cancel]

theorem lvBasis_φpow_letter (i : ZMod n) (k : ℕ) {x : T.V ⊗[Qp] B} (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V)) ^ k) x ∈ DcrisL PD T.ρ (W.emb (i + k)) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ, ← add_assoc]
    exact lvBasis_φ_letter PD T.ρ (W.emb_σ (i + k)) ih

theorem lvBasis_φpow_pre (hspan : Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ)
    (h3 : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))
    (c : ZMod n) (k : ℕ) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb c)) :
    ∃ d' ∈ DcrisL PD T.ρ (W.emb (c - k)), ((φVB PD (LL := LL) (V := T.V)) ^ k) d' = d := by
  induction k with
  | zero => exact ⟨d, by simpa using hd, by simp⟩
  | succ k ih =>
    obtain ⟨d₁, hd₁, rfl⟩ := ih
    obtain ⟨d', hd', rfl⟩ := lvBasis_letter_pre hspan h3 _ hd₁
    refine ⟨d', ?_, ?_⟩
    · rw [Nat.cast_succ, ← sub_sub]
      exact hd'
    · rw [pow_succ, Module.End.mul_apply]

end Formalism.MainNotions.N.Ln03.Pf

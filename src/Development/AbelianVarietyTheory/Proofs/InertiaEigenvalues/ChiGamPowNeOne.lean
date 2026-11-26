module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCoeffOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModulePeriodMapToBcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisConvergingOpenDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponent
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

section Filt

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

end Filt

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem tmul_mem_filV_of_mem_fil (n : ℤ) (v : V) {y : BdR} (hy : y ∈ PD.Fil n) :
    v ⊗ₜ[Qp] y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) n := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  exact ⟨v ⊗ₜ[Qp] (⟨y, hy⟩ : (PD.Fil n).restrictScalars Qp), by simp⟩

private theorem fil_antitone' {a b : ℤ} (h : b ≤ a) : PD.Fil a ≤ PD.Fil b := by
  induction a, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem filV_antitone' {a b : ℤ} (h : b ≤ a) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b := by
  intro x hx
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simpa using tmul_mem_filV_of_mem_fil PD b v (fil_antitone' PD h y.2)
  | add x y hx hy =>
    rw [LinearMap.map_add]
    exact add_mem hx hy

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] in
private theorem exists_mem_filV' (x : V ⊗[Qp] BdR) : ∃ n, x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) n := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v y =>
    obtain ⟨n, hn⟩ := PD.Fil_exh y
    exact ⟨n, tmul_mem_filV_of_mem_fil PD n v hn⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨min n₁ n₂, add_mem (filV_antitone' PD (min_le_left _ _) h₁)
      (filV_antitone' PD (min_le_right _ _) h₂)⟩
end

section
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O)

private theorem mulVR_tmul' (β : BdR) (v : T.V) (y : BdR) :
    _root_.Formalism.BasicNotions.mulVR T β (v ⊗ₜ[Qp] y) = v ⊗ₜ[Qp] (β * y) := by
  simp [_root_.Formalism.BasicNotions.mulVR]

private theorem mulVR_mulVR' (β γ : BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T β (_root_.Formalism.BasicNotions.mulVR T γ x) = _root_.Formalism.BasicNotions.mulVR T (β * γ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', mul_assoc]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem mulVR_mem_compKer (ι : LL →ₐ[Qp] BdR) (β : BdR) {x : T.V ⊗[Qp] BdR}
    (hx : x ∈ _root_.Formalism.BasicNotions.compKer T ι) : _root_.Formalism.BasicNotions.mulVR T β x ∈ _root_.Formalism.BasicNotions.compKer T ι := by
  unfold _root_.Formalism.BasicNotions.compKer at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, y, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c, _root_.Formalism.BasicNotions.mulVR T β y, ?_⟩
    rw [map_sub, LinearMap.map_smul, mulVR_mulVR', mulVR_mulVR', mul_comm]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [LinearMap.map_add]
    exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ c hx
end

private theorem mulRight_mem_filV_lemma_4 {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type}
    [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K]
    [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B]
    [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {p n : ℤ} {β : BdR}
    (hβ : β ∈ PD.Fil p) {x : T.V ⊗[Qp] BdR} (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n) :
    _root_.Formalism.BasicNotions.mulVR T β x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (p + n) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV at hx
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype,
      mulVR_tmul']
    exact tmul_mem_filV_of_mem_fil PD _ v (PD.Fil_mul _ _ _ _ hβ y.2)
  | add x y hx hy =>
    simp only [LinearMap.map_add]
    exact add_mem hx hy

section
variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {BdR : Type}
    [CommRing BdR] [Algebra Qp BdR] {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O)

private theorem mulVR_add' (β γ : BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T (β + γ) x = _root_.Formalism.BasicNotions.mulVR T β x + _root_.Formalism.BasicNotions.mulVR T γ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', add_mul, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

private theorem mulVR_zero' (x : T.V ⊗[Qp] BdR) : _root_.Formalism.BasicNotions.mulVR T 0 x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp only [mulVR_tmul', zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

private theorem mulVR_sum {ι : Type} (s : Finset ι) (f : ι → BdR) (x : T.V ⊗[Qp] BdR) :
    _root_.Formalism.BasicNotions.mulVR T (∑ i ∈ s, f i) x = ∑ i ∈ s, _root_.Formalism.BasicNotions.mulVR T (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mulVR_zero']
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, mulVR_add', ih]

private theorem smul_sub_mulVR_mem_compKer (ι : LL →ₐ[Qp] BdR) (c : LL) (x : T.V ⊗[Qp] BdR) :
    c • x - _root_.Formalism.BasicNotions.mulVR T (ι c) x ∈ _root_.Formalism.BasicNotions.compKer T ι := by
  unfold _root_.Formalism.BasicNotions.compKer
  exact Submodule.subset_span ⟨c, x, rfl⟩
end

theorem _root_.GlobalTheory.HWL.Cmp.filt_expansion_component : ∀ {G : Type} [Group G]
    [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀]
    [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B]
    [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR]
    [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR]
    [IsScalarTower Qp K₀ BdR] (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 →
    ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR)
    (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR),
    _root_.Formalism.BasicNotions.mulVR T (tS ^ w) z - ∑ j, _root_.Formalism.BasicNotions.mulVR T (b j) (D j) ∈ _root_.Formalism.BasicNotions.compKer T ι →
    (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈
      PD.Fil (m : ℤ)) →
    (∀ k : ℤ, L k - ∑ j, _root_.GlobalTheory.HWL.Cmp.cz (e j) (k + (w : ℤ)) • D j ∈ _root_.Formalism.BasicNotions.compKer T ι) →
    ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ,
      _root_.Formalism.BasicNotions.mulVR T (tS ^ a) (_root_.Formalism.BasicNotions.mulVR T pk z) -
        _root_.Formalism.BasicNotions.mulVR T pk (∑ k ∈ Finset.range M, _root_.Formalism.BasicNotions.mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈
      _root_.Formalism.BasicNotions.compKer T ι ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ T ι tS pk
    hunit htS r w z D b e L hz hb hL a hLa
  classical
  set C := _root_.Formalism.BasicNotions.compKer T ι with hC

  set t : BdRˣ := hunit.unit with ht_def
  have htt : (t : BdR) = tS := hunit.unit_spec
  set τ : ℤ → BdR := fun n => ((t ^ n : BdRˣ) : BdR) with hτ_def
  have τ_add : ∀ m n : ℤ, τ (m + n) = τ m * τ n := fun m n => by
    simp only [hτ_def, zpow_add, Units.val_mul]
  have τ_nat : ∀ n : ℕ, τ n = tS ^ n := fun n => by
    simp only [hτ_def, zpow_natCast, Units.val_pow_eq_pow_val, htt]

  obtain ⟨q₁, hq₁⟩ := PD.Fil_exh (1 : BdR)
  have hpow : ∀ n : ℕ, tS ^ n ∈ PD.Fil (q₁ + n) := by
    intro n
    induction n with
    | zero => simpa using hq₁
    | succ n ih =>
      rw [pow_succ]
      convert PD.Fil_mul _ _ _ _ ih htS using 2
      push_cast
      ring
  obtain ⟨p, hp⟩ := PD.Fil_exh pk
  set β₀ : BdR := pk * τ ((a : ℤ) - w) with hβ₀_def
  obtain ⟨q₂, hq₂⟩ := PD.Fil_exh β₀
  choose dj hdj using fun j => exists_mem_filV' PD (LL := LL) (D j)
  set d : ℤ := -∑ j, |dj j| with hd_def
  have hDd : ∀ j, D j ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d := fun j => by
    refine filV_antitone' PD ?_ (hdj j)
    have h1 : |dj j| ≤ ∑ i, |dj i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (dj i)) (Finset.mem_univ j)
    have h2 := neg_abs_le (dj j)
    linarith
  have hmulS : ∀ {β : BdR} {q n : ℤ} {x : T.V ⊗[Qp] BdR}, β ∈ PD.Fil q →
      x ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n →
      _root_.Formalism.BasicNotions.mulVR T β x ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q + n) := by
    intro β q n x hβ hx
    obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (mulVR_mem_compKer T ι β hy) (mulRight_mem_filV_lemma_4 PD T hβ hy')
  have hsupmono : ∀ {m n : ℤ}, n ≤ m → C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) m ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) n := fun h => sup_le_sup_left (filV_antitone' PD h) _

  have hcoeff : ∀ (f : PowerSeries LL) (k : ℕ), _root_.GlobalTheory.HWL.Cmp.cz f (k : ℤ) = PowerSeries.coeff k f := by
    intro f k
    simp [_root_.GlobalTheory.HWL.Cmp.cz]
  have hLC : ∀ i : ℤ, i < -(w : ℤ) → L i ∈ C := by
    intro i hi
    have h := hL i
    simpa [_root_.GlobalTheory.HWL.Cmp.cz_neg _ (show i + (w : ℤ) < 0 by omega)] using h
  have hLF : ∀ i : ℤ, L i ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d := by
    intro i
    have hs : ∑ j, _root_.GlobalTheory.HWL.Cmp.cz (e j) (i + (w : ℤ)) • D j ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) d :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hDd j)
    have h := Submodule.add_mem_sup (hL i) hs
    rwa [sub_add_cancel] at h

  set H : ℤ → T.V ⊗[Qp] BdR := fun i => _root_.Formalism.BasicNotions.mulVR T (pk * τ (i + a)) (L i) with hH_def
  have hH0 : ∀ i : ℤ, i < -(a : ℤ) → H i = 0 := fun i hi => by
    simp only [hH_def, hLa i hi, map_zero]
  have hHC : ∀ i : ℤ, i < -(w : ℤ) → H i ∈ C := fun i hi =>
    mulVR_mem_compKer T ι _ (hLC i hi)
  have hHF : ∀ (N : ℕ) (i : ℤ), (N : ℤ) ≤ i + a →
      H i ∈ C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (N + (p + q₁ + d)) := by
    intro N i hi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, i + a = n := ⟨(i + a).toNat, by omega⟩
    have hβ : pk * τ (i + a) ∈ PD.Fil (p + (q₁ + n)) := by
      rw [hn, τ_nat]
      exact PD.Fil_mul _ _ _ _ hp (hpow n)
    refine hsupmono ?_ (hmulS hβ (hLF i))
    omega

  have hbase : ∑ k ∈ Finset.range w, H ((k : ℤ) - w) - ∑ k ∈ Finset.range a, H ((k : ℤ) - a) ∈ C := by
    have e1 : ∑ k ∈ Finset.range (a + w), H ((k : ℤ) - ((a + w : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) +
          ∑ k ∈ Finset.range w, H ((k : ℤ) - w) := by
      rw [Finset.sum_range_add]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      push_cast
      ring
    have e2 : ∑ k ∈ Finset.range (a + w), H ((k : ℤ) - ((a + w : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range a, H ((k : ℤ) - a) := by
      rw [add_comm a w, Finset.sum_range_add, Finset.sum_eq_zero (fun k hk => hH0 _ ?_), zero_add]
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        push_cast
        ring
      · have := Finset.mem_range.mp hk
        push_cast
        omega
    have hC1 : ∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) ∈ C :=
      Submodule.sum_mem _ fun k hk => hHC _ (by have := Finset.mem_range.mp hk; push_cast; omega)
    have hrw : ∑ k ∈ Finset.range w, H ((k : ℤ) - w) - ∑ k ∈ Finset.range a, H ((k : ℤ) - a) =
        -∑ k ∈ Finset.range a, H ((k : ℤ) - ((a + w : ℕ) : ℤ)) := by
      rw [← e2, e1]
      abel
    rw [hrw]
    exact neg_mem hC1
  have hshift : ∀ N : ℕ, ∑ k ∈ Finset.range (N + w), H ((k : ℤ) - w) -
      ∑ k ∈ Finset.range (N + a), H ((k : ℤ) - a) ∈ C := by
    intro N
    induction N with
    | zero => simpa using hbase
    | succ N ih =>
      rw [show N + 1 + w = (N + w) + 1 by ring, show N + 1 + a = (N + a) + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have heq : H (((N + w : ℕ) : ℤ) - w) = H (((N + a : ℕ) : ℤ) - a) := by
        congr 1
        push_cast
        ring
      rw [heq]
      convert ih using 1
      abel

  refine ⟨-(min (p + q₁ + d) (q₂ + w + d)), fun M => ?_⟩
  have hmin1 := min_le_left (p + q₁ + d) (q₂ + w + d)
  have hmin2 := min_le_right (p + q₁ + d) (q₂ + w + d)
  have hbnd1 : C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (M + (p + q₁ + d)) ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - -(min (p + q₁ + d) (q₂ + w + d))) :=
    hsupmono (by omega)
  have hbnd2 : C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q₂ + ((M + w : ℕ) : ℤ) + d) ≤
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) ((M : ℤ) - -(min (p + q₁ + d) (q₂ + w + d))) :=
    hsupmono (by push_cast; omega)

  have hτw : τ ((a : ℤ) - w) * tS ^ w = tS ^ a := by
    rw [← τ_nat w, ← τ_add, sub_add_cancel, τ_nat]
  have eqB : _root_.Formalism.BasicNotions.mulVR T (tS ^ a) (_root_.Formalism.BasicNotions.mulVR T pk z) = _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) := by
    rw [mulVR_mulVR', mulVR_mulVR', hβ₀_def, mul_assoc, hτw, mul_comm]
  have eqC : _root_.Formalism.BasicNotions.mulVR T pk (∑ k ∈ Finset.range M, _root_.Formalism.BasicNotions.mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) =
      ∑ k ∈ Finset.range M, H ((k : ℤ) - a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVR_mulVR', hH_def]
    dsimp only
    rw [sub_add_cancel, τ_nat]
  have m1 : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) ∈ C := by
    have h := mulVR_mem_compKer T ι β₀ hz
    rwa [map_sub, map_sum] at h
  have hstep : ∀ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) -
      (∑ k ∈ Finset.range (M + w), PowerSeries.coeff k (e j) • _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (D j) +
        _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
          ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j)) ∈ C := by
    intro j
    have hsplit : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) =
        ∑ k ∈ Finset.range (M + w),
          _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (_root_.Formalism.BasicNotions.mulVR T (ι (PowerSeries.coeff k (e j))) (D j)) +
        _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
          ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) := by
      rw [mulVR_mulVR']
      rw [show β₀ * b j = β₀ * (∑ k ∈ Finset.range (M + w), ι (PowerSeries.coeff k (e j)) * tS ^ k) +
          β₀ * (b j - ∑ k ∈ Finset.range (M + w), ι (PowerSeries.coeff k (e j)) * tS ^ k) by ring,
        mulVR_add', Finset.mul_sum, mulVR_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulVR_mulVR']
      exact congrArg (fun β => _root_.Formalism.BasicNotions.mulVR T β (D j)) (by ring)
    rw [hsplit, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h := mulVR_mem_compKer T ι (β₀ * tS ^ k)
      (smul_sub_mulVR_mem_compKer T ι (PowerSeries.coeff k (e j)) (D j))
    rw [map_sub, LinearMap.map_smul] at h
    rw [← neg_sub]
    exact neg_mem h
  have m2 := Submodule.sum_mem C (t := Finset.univ) fun j _ => hstep j
  rw [Finset.sum_sub_distrib] at m2
  have hβk : ∀ k : ℕ, pk * τ ((k : ℤ) - w + a) = β₀ * tS ^ k := fun k => by
    rw [show (k : ℤ) - w + a = ((a : ℤ) - w) + k by ring, τ_add, τ_nat, hβ₀_def, mul_assoc]
  have hterm : ∀ k : ℕ, _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) -
      H ((k : ℤ) - w) ∈ C := by
    intro k
    have h := mulVR_mem_compKer T ι (β₀ * tS ^ k) (hL ((k : ℤ) - w))
    simp only [sub_add_cancel, hcoeff] at h
    have h' := neg_mem h
    rw [← map_neg, neg_sub] at h'
    rw [hH_def]
    dsimp only
    rw [hβk k, ← map_sub]
    exact h'
  have m3 := Submodule.sum_mem C (t := Finset.range (M + w)) fun k _ => hterm k
  rw [Finset.sum_sub_distrib] at m3
  have m4 := hshift M
  have eqD : ∑ k ∈ Finset.range (M + a), H ((k : ℤ) - a) =
      ∑ k ∈ Finset.range M, H ((k : ℤ) - a) + ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) :=
    Finset.sum_range_add _ _ _
  have m5 : ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) ∈
      C ⊔ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (M + (p + q₁ + d)) :=
    Submodule.sum_mem _ fun k _ => hHF M _ (by push_cast; omega)
  have m6 : ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
      ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := T.V) (q₂ + ((M + w : ℕ) : ℤ) + d) :=
    Submodule.sum_mem _ fun j _ => mulRight_mem_filV_lemma_4 PD T (PD.Fil_mul _ _ _ _ hq₂ (hb j (M + w)))
      (hDd j)
  have eqA : ∑ j, ∑ k ∈ Finset.range (M + w), PowerSeries.coeff k (e j) • _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (D j) =
      ∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [LinearMap.map_smul]
  rw [Finset.sum_add_distrib, eqA] at m2
  rw [eqB, eqC]
  have hX : _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ k ∈ Finset.range M, H ((k : ℤ) - a) =
      (_root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (tS ^ w) z) - ∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j))) +
      (∑ j, _root_.Formalism.BasicNotions.mulVR T β₀ (_root_.Formalism.BasicNotions.mulVR T (b j) (D j)) -
        (∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) +
          ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
            ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j))) +
      (∑ k ∈ Finset.range (M + w), _root_.Formalism.BasicNotions.mulVR T (β₀ * tS ^ k) (∑ j, PowerSeries.coeff k (e j) • D j) -
        ∑ k ∈ Finset.range (M + w), H ((k : ℤ) - w)) +
      (∑ k ∈ Finset.range (M + w), H ((k : ℤ) - w) - ∑ k ∈ Finset.range (M + a), H ((k : ℤ) - a)) +
      ∑ k ∈ Finset.range a, H (((M + k : ℕ) : ℤ) - a) +
      ∑ j, _root_.Formalism.BasicNotions.mulVR T (β₀ * (b j - ∑ k ∈ Finset.range (M + w),
        ι (PowerSeries.coeff k (e j)) * tS ^ k)) (D j) := by
    rw [eqD]
    abel
  rw [hX]
  refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) (hbnd1 m5))
    (hbnd2 (Submodule.mem_sup_right m6))
  · exact Submodule.mem_sup_left m1
  · exact Submodule.mem_sup_left m2
  · exact Submodule.mem_sup_left m3
  · exact Submodule.mem_sup_left m4

end GlobalTheory.HWL.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationEstimateExpansionTensorBdRComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]  (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (tS pk : BdR), IsUnit tS → tS ∈ PD.Fil 1 → ∀ (r w : ℕ) (z : T.V ⊗[Qp] BdR) (D : Fin r → T.V ⊗[Qp] BdR) (b : Fin r → BdR) (e : Fin r → PowerSeries LL) (L : ℤ → T.V ⊗[Qp] BdR), mulVR T (tS ^ w) z - ∑ j, mulVR T (b j) (D j) ∈ compKer T ι → (∀ (j : Fin r) (m : ℕ), b j - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (e j)) * tS ^ k ∈ PD.Fil (m : ℤ)) → (∀ k : ℤ, L k - ∑ j, cz (e j) (k + (w : ℤ)) • D j ∈ compKer T ι) → ∀ a : ℕ, (∀ k : ℤ, k < -(a : ℤ) → L k = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS ^ a) (mulVR T pk z) - mulVR T pk (∑ k ∈ Finset.range M, mulVR T (tS ^ k) (L ((k : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.HWL.Cmp.filt_expansion_component | exact GlobalTheory.HWL.Cmp.filt_expansion_component | (intros; apply GlobalTheory.HWL.Cmp.filt_expansion_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnityStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnity
namespace GlobalTheory

open PowerSeries in
theorem powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  classical
  obtain ⟨z, rfl⟩ : X ∣ y := by rwa [PowerSeries.X_dvd_iff]
  have hs : HasSubst (X * z) := HasSubst.of_constantCoeff_zero' hy
  have hu1 : coeff 1 (X * z) = constantCoeff z := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [hu1] at hu

  have hc : ∀ n, coeff n (a.subst (X * z)) =
      ∑ d ∈ Finset.range (n + 1), coeff d a * coeff (n - d) (z ^ d) := by
    intro n
    rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)),
        smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

  have main : ∀ k, 0 < k → coeff k a = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have h1 := hc k
      rw [ha, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, map_pow] at h1
      · have h2 : coeff k a * (1 - constantCoeff z ^ k) = 0 := by
          rw [mul_sub, mul_one, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm (hu k hk)
      · intro d hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [coeff_one, hk.ne']
        · rw [ih d (Finset.mem_range.mp hd) hd0, zero_mul]
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_C, if_neg (Nat.succ_ne_zero n)]
    exact main (n + 1) (Nat.succ_pos n)

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity : ∀ (L : Type) [Field L] (y : PowerSeries L), PowerSeries.constantCoeff y = 0 → (∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) → ∀ a : PowerSeries L, (PowerSeries.subst y a : PowerSeries L) = a → a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  first | exact @GlobalTheory.powerSeries_eq_C_of_subst_eq_self | exact GlobalTheory.powerSeries_eq_C_of_subst_eq_self | (intros; apply GlobalTheory.powerSeries_eq_C_of_subst_eq_self <;> assumption)
end

noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

variable {R : WSer Γ} {b₀ : LetA O n →+* LL ⊗[Qp] B} {tS zS : BdR}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

open Classical in
def levOf {Dc : Disc R b₀ tS zS} {Mo : WN E zl} (bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] B) :=
  if h : IsCrys PD T.ρ then (Fr T h).lev bT i ζ else 0

set_option maxHeartbeats 1000000 in
theorem nonempty_wCmp [NeZero n] (Dc : Disc R b₀ tS zS) (Mo : WN E zl) {ιdR : Ai →+* BdR} {p1 : Ai}
    {βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR}
    {bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B} (hP : IsPer Mo b₀ ιdR p1 βdR bT)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T)
    (hinv : ∀ a : LetA LL n, γL R Γ.gam a = a → ∃ c, a = cst c) : Nonempty (WCmp Mo ιdR p1 tS zS) := by
  have pos : ∀ (T : LocLat G Qp LL O) (h : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = Frame.lev bT (Fr T h) i ζ :=
    fun T h i ζ => dif_pos h
  have neg : ∀ (T : LocLat G Qp LL O) (_ : ¬ IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = 0 := fun T h i ζ => dif_neg h
  have hmem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i) := by
    intro T i ζ x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_mem hP h _ i ζ x k
    · rw [neg T h]; exact Submodule.zero_mem _
  have hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)), ∃ m : ℤ, ∀ k < m, levOf bT Fr T i ζ x k = 0 := by
    intro T i ζ x
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact ⟨_, Frame.lev_supp bT _ i ζ x⟩
    · rw [neg T h]; exact ⟨0, fun _ _ => rfl⟩
  have hneg : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)) (k : ℤ), k < 0 → levOf bT Fr T i 1 x k = 0 := by
    intro T i x k hk
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_one_neg bT _ i x k hk
    · rw [neg T h]; rfl
  have hsmul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (α : LetA O n) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ (α • x) k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ α) • levOf bT Fr T i ζ x (k - (j : ℤ)) := by
    intro T i ζ α x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_smul bT _ i ζ α x k
    · rw [neg T h]; simp
  have hsmul0 : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (α : LetA O n) (x : ↥(Mo.N T)), levOf bT Fr T i 1 (α • x) 0 =
      PowerSeries.constantCoeff (R.lev i 1 α) • levOf bT Fr T i 1 x 0 := by
    intro T i α x
    rw [hsmul, finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [hneg T i x _ (by omega), smul_zero]
  let cmp : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B := fun T =>
    ∑ i : ZMod n, (Pi.evalAddMonoidHom (fun _ : ℤ => T.V ⊗[Qp] B) 0).comp (levOf bT Fr T i 1)
  have hcmp : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T x = ∑ i : ZMod n, levOf bT Fr T i 1 x 0 := by
    intro T x
    simp [cmp]
  have hcmpE : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)), cmp T ((letE i : LetA O n) • x) = levOf bT Fr T i 1 x 0 := by
    intro T i x
    rw [hcmp, Finset.sum_eq_single i]
    · rw [hsmul0, Dc.lev_letE]; simp
    · intro j _ hj
      rw [hsmul0, Dc.lev_letE]; simp [hj]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  have hmap : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
      ∀ (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ),
      levOf bT Fr T' i ζ ⟨E.map f (x : E.DD T), hx⟩ k =
        AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (levOf bT Fr T i ζ x k) := by
    intro T T' f h h' i ζ x hx k
    rw [pos T h, pos T' h']
    exact Frame.lev_map hP hinv f h h' _ _ i ζ x hx k
  let levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] BdR) := fun T i ζ =>
    ((ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.compLeft ℤ).comp (levOf bT Fr T i ζ)
  have hN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levOf bT Fr T i ζ x k) :=
    fun _ _ _ _ _ => rfl
  refine ⟨{
    cmp := cmp
    cmp_smul := fun T c x => ?_
    cmp_π := fun T x => ?_
    cmp_mem := fun T x => ?_
    cmp_letter := fun T i x => by rw [hcmpE]; exact hmem T i 1 x 0
    cmp_map := fun f h h' x hx => by simp only [hcmp, hmap f h h', map_sum]
    levN := levN
    levN_supp := fun T i ζ x => ?_
    levN_smul := fun T i ζ α x k => ?_
    levN_map := fun {T T'} f h h' i ζ x hx k => ?_
    levB := levOf bT Fr
    levB_mem := hmem
    levB_supp := hsupp
    levN_eq := hN
    cmp_eq := fun T _ => hcmpE T
    levB_φ := fun T h i ζ hζ x m hx k => by
      simp only [pos T h]; exact Frame.lev_φ hP h _ i ζ hζ x m hx k
    levB_Γ := fun T h g i ζ ζ' j a h1 h2 h3 x hx k => by
      simp only [pos T h]; exact Frame.lev_Γ bT _ g i ζ ζ' j a h1 h2 h3 x hx k
    βdR := βdR
    βdR_tmul := hP.tmul
    levN_dR := fun T h i ζ ι h1 h2 x k y hy a ha => ?_ }⟩
  · have : c • x = algebraMap O (LetA O n) c • x := Subtype.ext (algebraMap_smul (LetA O n) c (x : E.DD T)).symm
    rw [this, hcmp, hcmp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul0, AlgHom.commutes]
    simp [PowerSeries.algebraMap_apply]
  · rw [hcmp]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨e, he, -, h3⟩ := R.lev_π i 1 ⟨0, by simp⟩
    have h4 := congrArg PowerSeries.constantCoeff h3
    rw [map_add (f := _), map_mul, he] at h4
    have h5 : PowerSeries.constantCoeff (R.lev i 1 letπ) = 0 := by simpa using h4
    rw [hsmul0, h5, zero_smul]
  · rw [hcmp]
    exact Submodule.sum_mem _ fun i _ => (hmem T i 1 x 0).1
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    exact ⟨m, fun k hk => by rw [hN, hm k hk, map_zero]⟩
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    have hz : ∀ j : ℕ, j ∉ Finset.range ((k - m).toNat + 1) → levOf bT Fr T i ζ x (k - (j : ℤ)) = 0 := by
      intro j hj
      have : (k - m).toNat + 1 ≤ j := by simpa using hj
      exact hm _ (by omega)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hN, hsmul, finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)),
      finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)), map_sum]
    · simp only [map_smul, hN]
    · intro j hj
      by_contra hc
      exact hj (by simp only [hN, hz j hc, map_zero, smul_zero])
    · intro j hj
      by_contra hc
      exact hj (by simp only [hz j hc, smul_zero])
  · rw [hN, hN, hmap f h h']
    induction levOf bT Fr T i ζ x k using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b => simp [ιV]
  · rw [hP.dR T h x k y hy]
    refine GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component PD T ι tS (ιdR p1 ^ k) (Dc.ι_tb ▸ Dc.tb_unit.map PD.ι) Dc.tS_mem (Fr T h).r (Fr T h).w _
      (fun j => ιV PD (LL := LL) (V := T.V) ((Fr T h).d bT j)) _ (fun j => Dc.ex i ζ ((Fr T h).a x j)) _
      (Frame.dR_basis hP h (Fr T h) ι x) (fun j m => Dc.taylor i ζ ι h1 h2 _ m) (fun k => ?_) a ha
    rw [hN, pos T h]
    exact Frame.dR_lev (Fr T h) i ζ ι h1 h2 x k

end Generic

theorem chi_gam_pow_ne_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (hG : Good K s LL) (Γ : GamS P K s LL) (k : ℕ) (hk : 0 < k) :
    algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ Γ.gam : ↥(OL LL)) ^ k ≠ 1 := by
  intro h
  obtain ⟨⟨lam, -, h1, h2, ⟨g, hg⟩, -⟩, -⟩ := GlobalTheory.HWL.Coord.exists_gamma_coordinates l P K s LL hG Γ
  have h3 : Γ.gam ^ k = 1 := by
    apply Γ.χΓ_inj
    rw [map_pow, map_one]
    apply Units.ext
    apply Subtype.ext
    simpa using h
  have h4 : lam (g ^ k) = 1 := by
    rw [h1, Subgroup.coe_pow, map_pow, (h2 g).mp hg, h3]
  rw [map_pow, hg, ← ofAdd_nsmul, ofAdd_eq_one] at h4
  simp at h4
  omega

set_option maxHeartbeats 1000000 in
theorem nonempty_cmpS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
    IoW I → ∀ (E : WEt I) (Mo : NS E), Nonempty (CmpS Mo) := by
  intro l _ P AI hT K s LL hG Γ R I hI E Mo
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.HWLBeta.exists_beta l P AI hT LL
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_evaluation_convergent_series_Bcris l P AI hT K s LL hG Γ R I hI β hβ
  obtain ⟨Dc, hC, ht⟩ := GlobalTheory.T.exists_openDiscConvergentRing_with_expansions l P AI hT K s LL hG Γ R I hI β hβ J hJ (GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta l P K s LL Γ R)
    (GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image l P AI hT K s LL hG Γ R I hI β hβ)
  obtain ⟨βdR, bT, hP⟩ := GlobalTheory.T.exists_wachModule_periodMap_to_bcris l P AI hT K s LL hG Γ R I hI β hβ E Mo
    (GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi l P AI K s LL hG Γ R I hI E Mo)
  have hF : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → Nonempty (Frame Dc Mo T) := by
    intro T h
    obtain ⟨nb⟩ := GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hG Γ R I hI E Mo T h
    obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_wachLattice_matrices_gamma_phi Mo T _ nb
    obtain ⟨U, V, w, k1, -, k3, k4, Cm, k5⟩ := GlobalTheory.T.exists_invariant_basis_converging_open_disc l P K s LL hG Γ R _ m m' Gm Pm Pm' h1 h2 h3 h4
    refine ⟨{
      r := _, w := w, m := m, nb := nb, U := U, V := V, UV := k1
      U_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).1
      V_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).2
      Gm := Gm, Gm_def := h5
      GU := fun g => ?_
      Pm := Pm, Pm_def := h6, Cm := Cm
      PU := ?_ }⟩
    · rw [funext (γL_apply R g)]
      exact k4 g
    · have e1 : ⇑(φL ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) (P.PD K).p) = fun a k =>
          PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1)) := by
        funext a
        rw [φL_apply, P.PD_p]
      have e2 : toL ↥(OL LL) ↥LL.1 _ (R.Q ^ m) = toLL R.Q ^ m := (toL ↥(OL LL) ↥LL.1 _).map_pow R.Q m
      rw [e1]
      exact k5.trans (congrArg (fun q : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) => q • (U * Cm.map cst)) e2.symm)
  refine nonempty_wCmp Dc Mo hP (fun T h => (hF T h).some) fun a ha => ?_
  refine ⟨fun i => PowerSeries.constantCoeff (a i), funext fun i => ?_⟩
  refine GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity _ (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ Γ.gam PowerSeries.X)) ?_ ?_ (a i) ?_
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X _).1, map_zero]
  · intro k hk
    rw [PowerSeries.coeff_map, (R.γ₀_X _).2]
    exact chi_gam_pow_ne_one hG Γ k hk
  · rw [γL_apply] at ha
    exact congrFun ha i

end GlobalTheory.HWL.Cmp

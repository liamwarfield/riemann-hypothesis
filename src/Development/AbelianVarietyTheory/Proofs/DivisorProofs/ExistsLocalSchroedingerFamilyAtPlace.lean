module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMemSpanCoordinateBoxIndicators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMemSpanCoordinateBoxIndicators
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.BoxDecomp

open Topology Filter

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem ball_mem_nhds_zero (v : Pl (F := F)) (N : ℕ) :
    {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} ∈ 𝓝 (0 : Fv F v) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := (π : v.adicCompletion F) with hp
  have hpv : Valued.v p = WithZero.exp (-1) := by
    rw [hp, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hrv : Valued.v (p ^ N) = WithZero.exp (-(N : ℤ)) := by
    rw [map_pow, hpv, ← WithZero.exp_nsmul]; congr 1; simp
  have hr : Valued.v (p ^ N) ≠ 0 := by rw [hrv]; exact WithZero.exp_ne_zero
  rw [Valued.mem_nhds_zero]
  have h' : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (p ^ N) ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 _ h', fun y hy => ?_⟩
  have := (Valuation.restrict_lt_iff _).1 hy
  rw [hrv] at this
  exact le_of_lt this

theorem exists_ball_subset (v : Pl (F := F)) {s : Set (Fv F v)} (hs : s ∈ 𝓝 (0 : Fv F v)) :
    ∃ N : ℕ, {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨(-(WithZero.log g)).toNat + 1, fun y hy => hγ ?_⟩
  show (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hy ?_
  have hlt : WithZero.exp (-((((-(WithZero.log g)).toNat + 1 : ℕ)) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.2 (by omega)
  rwa [WithZero.exp_log hg0] at hlt

def B (v : Pl (F := F)) (κ : Type) (N : ℕ) : Set (κ → Fv F v) :=
  {x | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))}

theorem B_anti {κ : Type} {N M : ℕ} (h : N ≤ M) : B v κ M ⊆ B v κ N := fun x hx i =>
  (hx i).trans (WithZero.exp_le_exp.2 (by omega))

theorem zero_mem_B (κ : Type) (N : ℕ) : (0 : κ → Fv F v) ∈ B v κ N := fun i => by simp

theorem sub_mem_B {κ : Type} {N : ℕ} {x y : κ → Fv F v} (hx : x ∈ B v κ N) (hy : y ∈ B v κ N) :
    x - y ∈ B v κ N := fun i =>
  (Valuation.map_sub _ _ _).trans (max_le (hx i) (hy i))

theorem add_mem_B {κ : Type} {N : ℕ} {x y : κ → Fv F v} (hx : x ∈ B v κ N) (hy : y ∈ B v κ N) :
    x + y ∈ B v κ N := fun i =>
  (Valuation.map_add _ _ _).trans (max_le (hx i) (hy i))

theorem neg_mem_B {κ : Type} {N : ℕ} {x : κ → Fv F v} (hx : x ∈ B v κ N) : -x ∈ B v κ N := fun i => by
  simpa using hx i

theorem B_mem_nhds (κ : Type) [Fintype κ] (N : ℕ) : B v κ N ∈ 𝓝 (0 : κ → Fv F v) := by
  have : B v κ N = Set.pi Set.univ fun _ => {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} := by
    ext x; simp [B]
  rw [this]
  exact set_pi_mem_nhds Set.finite_univ fun i _ => ball_mem_nhds_zero v N

theorem exists_B_subset (κ : Type) [Fintype κ] {s : Set (κ → Fv F v)} (hs : s ∈ 𝓝 (0 : κ → Fv F v)) :
    ∃ N : ℕ, B v κ N ⊆ s := by
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨I, -, t, ht, hts⟩ := hs
  choose Nf hNf using fun i => exists_ball_subset v (ht i)
  refine ⟨Finset.univ.sup Nf, fun x hx => hts fun i _ => hNf i ?_⟩
  exact (hx i).trans (WithZero.exp_le_exp.2 (by
    have := Finset.le_sup (f := Nf) (Finset.mem_univ i); omega))

theorem isOpen_box (κ : Type) [Fintype κ] (N : ℕ) (c : κ → Fv F v) :
    IsOpen {x : κ → Fv F v | x - c ∈ B v κ N} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ht : Tendsto (fun y : κ → Fv F v => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  refine Filter.mem_of_superset (ht (B_mem_nhds κ N)) fun y hy => ?_
  have : y - c = (y - x) + (x - c) := by abel
  show y - c ∈ B v κ N
  rw [this]; exact add_mem_B hy hx

theorem exists_invariant {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y u, u ∈ B v κ N → φ (y + u) = φ y := by
  have hloc : ∀ x : κ → Fv F v, ∃ N : ℕ, ∀ u ∈ B v κ N, φ (x + u) = φ x := by
    intro x
    have hlc : IsLocallyConstant fun u : κ → Fv F v => φ (x + u) :=
      hφ.1.comp_continuous (continuous_const_add x)
    have hO : {u : κ → Fv F v | φ (x + u) = φ x} ∈ 𝓝 (0 : κ → Fv F v) :=
      (hlc.isOpen_fiber (φ x)).mem_nhds (by simp)
    obtain ⟨N, hN⟩ := exists_B_subset κ hO
    exact ⟨N, fun u hu => hN hu⟩
  choose Nx hNx using hloc
  have hK : IsCompact (tsupport φ) := hφ.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => {y : κ → Fv F v | y - x ∈ B v κ (Nx x)})
    (fun x => isOpen_box κ (Nx x) x) (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using zero_mem_B κ (Nx y)⟩)
  refine ⟨t.sup Nx, fun N hN y u hu => ?_⟩
  have hsub : ∀ x ∈ t, u ∈ B v κ (Nx x) := fun x hx =>
    B_anti ((Finset.le_sup (f := Nx) hx).trans hN) hu
  by_cases hy : ∃ x ∈ t, y - x ∈ B v κ (Nx x)
  · obtain ⟨x, hx, hyx⟩ := hy
    have h1 : φ (y + u) = φ x := by
      have := hNx x ((y - x) + u) (add_mem_B hyx (hsub x hx))
      rwa [show x + ((y - x) + u) = y + u by abel] at this
    have h2 : φ y = φ x := by
      have := hNx x (y - x) hyx
      rwa [show x + (y - x) = y by abel] at this
    rw [h1, h2]
  · push_neg at hy
    have hyK : y ∉ tsupport φ := fun hyK => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
      exact hy x hx hyx
    have hyuK : y + u ∉ tsupport φ := fun hyK => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
      refine hy x hx ?_
      have := sub_mem_B hyx (hsub x hx)
      rwa [show y + u - x - u = y - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hyK, image_eq_zero_of_notMem_tsupport hyuK]

def BG (v : Pl (F := F)) (κ : Type) (N : ℕ) : AddSubgroup (κ → Fv F v) where
  carrier := B v κ N
  add_mem' := add_mem_B
  zero_mem' := zero_mem_B κ N
  neg_mem' := neg_mem_B

theorem mk_eq_iff {κ : Type} {N : ℕ} {x c : κ → Fv F v} :
    (x : (κ → Fv F v) ⧸ BG v κ N) = c ↔ x - c ∈ B v κ N := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := neg_mem_B h
    rwa [show -(-x + c) = x - c by abel] at this
  · intro h
    have := neg_mem_B h
    rwa [show -(x - c) = -x + c by abel] at this

theorem mem_span_boxes (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (φ : (κ → Fv F v) → ℂ) : φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ
      (Set.range fun c : κ → Fv F v => Set.indicator
        {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) := by
  classical
  intro hφ
  obtain ⟨N₀, hN₀⟩ := exists_invariant hφ
  refine ⟨N₀, fun N hN => ?_⟩
  have hK : IsCompact (tsupport φ) := hφ.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c => {y : κ → Fv F v | y - c ∈ B v κ N})
    (fun c => isOpen_box κ N c) (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using zero_mem_B κ N⟩)
  set Q : Finset ((κ → Fv F v) ⧸ BG v κ N) := t.image (QuotientAddGroup.mk (s := BG v κ N)) with hQ
  have heq : φ = ∑ q ∈ Q, φ q.out • Set.indicator
      {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) := by
    funext x
    have hterm : ∀ q : (κ → Fv F v) ⧸ BG v κ N, (φ q.out • Set.indicator
        {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) x =
        if (x : (κ → Fv F v) ⧸ BG v κ N) = q then φ q.out else 0 := by
      intro q
      have hm : (x ∈ {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))}) ↔
          (x : (κ → Fv F v) ⧸ BG v κ N) = q := by
        rw [← QuotientAddGroup.out_eq' q, mk_eq_iff, QuotientAddGroup.out_eq']
        rfl
      rw [Pi.smul_apply, Set.indicator_apply]
      by_cases h : (x : (κ → Fv F v) ⧸ BG v κ N) = q
      · rw [if_pos (hm.2 h), if_pos h, Pi.one_apply, smul_eq_mul, mul_one]
      · rw [if_neg (fun h' => h (hm.1 h')), if_neg h, smul_zero]
    rw [Finset.sum_apply]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · set q : (κ → Fv F v) ⧸ BG v κ N := (x : (κ → Fv F v) ⧸ BG v κ N)
      have hqx : q.out - x ∈ B v κ N := mk_eq_iff.1 (QuotientAddGroup.out_eq' q)
      have := hN₀ N hN x (q.out - x) hqx
      rw [show x + (q.out - x) = q.out by abel] at this
      exact this.symm
    · have hxK : x ∉ tsupport φ := fun hxK => by
        obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hxK)
        have hcQ : (c : (κ → Fv F v) ⧸ BG v κ N) ∈ Q :=
          Finset.mem_image_of_mem (QuotientAddGroup.mk (s := BG v κ N)) hc
        rw [← mk_eq_iff.2 hxc] at hcQ
        exact hx hcQ
      exact image_eq_zero_of_notMem_tsupport hxK
  rw [heq]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.out, rfl⟩)

end GlobalTheory.BoxDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMemSpanCoordinateBoxIndicatorsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) := by
  first | exact @GlobalTheory.BoxDecomp.mem_span_boxes | exact GlobalTheory.BoxDecomp.mem_span_boxes | (intros; apply GlobalTheory.BoxDecomp.mem_span_boxes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSpanBoxIndicatorSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSpanBoxIndicatorSchrodinger
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open Filter Topology

namespace GlobalTheory.SchrBox

theorem exists_cut {X ι : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (χ : ι → X → ℂ)
    (hχ : ∀ i x y, χ i (x + y) = χ i x * χ i y) {B : Set X} (hB : IsOpen B) (h0 : (0 : X) ∈ B)
    (hsep : ∀ z, z ∉ B → ∃ i, χ i z ≠ 1 ∧ ∀ u ∈ B, χ i u = 1) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ K, x - x₀ ∉ B → g x = 0 := by
  have hop : ∀ y : X, IsOpen {x | x - y ∈ B} := fun y => hB.preimage (continuous_id.sub continuous_const)
  have key := (hK.diff (hop x₀)).induction_on
    (p := fun T => ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ T, g x = 0)
    ⟨1, one_mem _, fun _ _ => rfl, fun _ h => h.elim⟩
    (fun s t hst ⟨g, hg, h1, h2⟩ => ⟨g, hg, h1, fun x hx => h2 x (hst hx)⟩)
    (fun s t hs ht => by
      obtain ⟨g, hg, h1, h2⟩ := hs
      obtain ⟨g', hg', h1', h2'⟩ := ht
      refine ⟨g * g', mul_mem hg hg', fun x hx => by simp [h1 x hx, h1' x hx], fun x hx => ?_⟩
      rcases hx with hx | hx
      · simp [h2 x hx]
      · simp [h2' x hx])
    (fun y hy => by
      obtain ⟨i, hi, hiB⟩ := hsep (y - x₀) hy.2
      have hne : 1 - χ i (y - x₀) ≠ 0 := sub_ne_zero.2 hi.symm
      have hx0 : ∀ x, χ i (-x₀) * χ i x = χ i (x - x₀) := fun x => by
        rw [← hχ]; congr 1; abel
      refine ⟨{x | x - y ∈ B}, mem_nhdsWithin_of_mem_nhds ((hop y).mem_nhds (by simpa using h0)),
        (1 - χ i (y - x₀))⁻¹ • (χ i (-x₀) • χ i - χ i (y - x₀) • 1), ?_, fun x hx => ?_, fun x hx => ?_⟩
      · exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
          (Subalgebra.smul_mem _ (one_mem _) _)) _
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, hiB _ hx]
        exact inv_mul_cancel₀ hne
      · have : χ i (x - x₀) = χ i (y - x₀) := by
          rw [show x - x₀ = (x - y) + (y - x₀) by abel, hχ, hiB _ hx, one_mul]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, this, sub_self, mul_zero])
  obtain ⟨g, hg, h1, h2⟩ := key
  exact ⟨g, hg, h1, fun x hx hx' => h2 x ⟨hx, hx'⟩⟩

theorem adjoin_mul_mem {X ι : Type} [AddCommGroup ι] (χ : ι → X → ℂ) (h0 : χ 0 = 1) (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (s : X → ℂ) {g : X → ℂ} (hg : g ∈ Algebra.adjoin ℂ (Set.range χ)) :
    g * s ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
  have key : ∀ f ∈ Submodule.span ℂ (Set.range fun i => χ i * s),
      g * f ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro f hf
      induction hf using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨i + j, by simp only [hχ, mul_assoc]⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
    | algebraMap r => intro f hf; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ hf
    | add a b _ _ ha hb => intro f hf; rw [add_mul]; exact add_mem (ha f hf) (hb f hf)
    | mul a b _ _ ha hb => intro f hf; rw [mul_assoc]; exact ha _ (hb f hf)
  exact key s (Submodule.subset_span ⟨0, by simp [h0]⟩)

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem isOpen_ball (n : ℤ) : IsOpen {y : Fv F v | Valued.v y ≤ WithZero.exp n} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : Fv F v | Valued.v y ≤ WithZero.exp n} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_ball_subset {U : Set (Fv F v)} {x : Fv F v} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

theorem exists_sep {ψ : AddChar (Fv F v) ℂ}
    (hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (n : ℤ) {z : Fv F v} (hz : ¬ Valued.v z ≤ WithZero.exp n) :
    ∃ t, ψ (z * t) ≠ 1 ∧ ∀ u, Valued.v u ≤ WithZero.exp n → ψ (u * t) = 1 := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hmem : ∀ u : Fv F v, u / c ∈ v.adicCompletionIntegers F ↔ Valued.v u ≤ WithZero.exp n := fun u => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hc, div_le_one₀ WithZero.exp_pos]
  have h1 := mt (hψ (z / c)).1 (mt (hmem z).1 hz)
  push Not at h1
  obtain ⟨y, hy, hy1⟩ := h1
  refine ⟨y / c, by rwa [show z * (y / c) = z / c * y by ring], fun u hu => ?_⟩
  rw [show u * (y / c) = u / c * y by ring]
  exact (hψ _).2 ((hmem u).2 hu) y hy

theorem indicator_box_mem_span : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro F _ _ v ψ hψ κ _ s hs hs0
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hs0
  have hx₀ : s x₀ ≠ 0 := hx₀
  have hU : {x | s x = s x₀} ∈ 𝓝 x₀ := (hs.1.isOpen_fiber (s x₀)).mem_nhds rfl
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  choose M hM using fun i => exists_ball_subset (ht i)
  refine ⟨x₀, Finset.univ.sup M, fun N hN => ?_⟩
  have hconst : ∀ x : κ → Fv F v, (∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))) → s x = s x₀ :=
    fun x hx => htU fun i _ => hM i N ((Finset.le_sup (f := M) (Finset.mem_univ i)).trans hN) _ (hx i)
  let χ : (κ → Fv F v) → (κ → Fv F v) → ℂ := fun b x => ψ (x ⬝ᵥ b)
  have hB : IsOpen {x : κ → Fv F v | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => (isOpen_ball (v := v) (-(N : ℤ))).preimage (continuous_apply (A := fun _ : κ => Fv F v) i)
  obtain ⟨g, hg, h1, h2⟩ := exists_cut χ (fun b x y => by simp only [χ, add_dotProduct, AddChar.map_add_eq_mul]) hB
    (by simp) (fun z hz => by
      simp only [Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      obtain ⟨t, ht1, ht2⟩ := exists_sep hψ _ hi
      exact ⟨Pi.single i t, by simpa only [χ, dotProduct_single] using ht1,
        fun u hu => by simpa only [χ, dotProduct_single] using ht2 _ (hu i)⟩) hs.2 x₀
  have hm := adjoin_mul_mem χ (by ext x; simp [χ])
    (fun i j => by ext x; simp only [χ, dotProduct_add, AddChar.map_add_eq_mul, Pi.mul_apply]) s hg
  have hle : Submodule.span ℂ (Set.range fun b => χ b * s) ≤
      Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨(0, b), by ext x; simp [schr, χ]⟩
  have := Submodule.smul_mem _ (s x₀)⁻¹ (hle hm)
  convert this using 1
  ext x
  by_cases hx : ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))
  · rw [Set.indicator_of_mem (by exact hx)]
    simp [h1 x hx, hconst x hx, hx₀]
  · rw [Set.indicator_of_notMem (by exact hx)]
    by_cases hxs : x ∈ tsupport s
    · simp [h2 x hxs hx]
    · simp [image_eq_zero_of_notMem_tsupport hxs]

end GlobalTheory.SchrBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSpanBoxIndicatorSchrodingerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  first | exact @GlobalTheory.SchrBox.indicator_box_mem_span | exact GlobalTheory.SchrBox.indicator_box_mem_span | (intros; apply GlobalTheory.SchrBox.indicator_box_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SchrLocModel

theorem box_mem : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) :=
  GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger

theorem decomp : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) :=
  GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators

def rhoSB {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) {κ : Type}
    [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) : Module.End ℂ (SB (κ → Fv F v)) where
  toFun φ := ⟨schr ψ w φ, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ w φ φ.2⟩
  map_add' φ φ' := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c φ := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem rhoSB_apply {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ)
    {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : SB (κ → Fv F v)) :
    ((rhoSB v ψ hψ w φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = schr ψ w φ := rfl

theorem schr_mem_span {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (s : (κ → R) → ℂ) (w : (κ → R) × (κ → R)) {f : (κ → R) → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)) :
    schr ψ w f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) := by
  let L : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) :=
    { toFun := schr ψ w
      map_add' := fun a b => by funext x; simp only [schr, Pi.add_apply, mul_add]
      map_smul' := fun c a => by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) ≤
      (Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨w', rfl⟩
    show schr ψ w (schr ψ w' s) ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)
    rw [schr_schr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + w', rfl⟩)
  exact hle hf

theorem schr_fst {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : κ → R) (f : (κ → R) → ℂ) : schr ψ (a, 0) f = fun x => f (x + a) := by
  funext x; simp [schr]

theorem span_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ)
    (hu : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ) (hs : s ∈ SB (κ → Fv F v)) (hs0 : s ≠ 0) :
    ∀ φ ∈ SB (κ → Fv F v),
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro φ hφ
  obtain ⟨x₀, N₀, hN₀⟩ := box_mem F v ψ hu κ s hs hs0
  obtain ⟨N₁, hN₁⟩ := decomp F v κ φ hφ
  refine Submodule.span_le.mpr ?_ (hN₁ (max N₀ N₁) (le_max_right _ _))
  rintro _ ⟨c, rfl⟩
  have h := schr_mem_span ψ s (x₀ - c, 0) (hN₀ (max N₀ N₁) (le_max_left _ _))
  rw [schr_fst] at h
  rw [SetLike.mem_coe]
  convert h using 1
  funext x
  have e : ∀ i, x i + (x₀ i - c i) - x₀ i = x i - c i := fun i => by ring
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.add_apply, Pi.sub_apply, e, Pi.one_apply]

end GlobalTheory.SchrLocModel

namespace GlobalTheory.SchrLocModel

theorem locCo_onto {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm]
    {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ) {Y : Type} [AddCommGroup Y] (Xm : Y →+ Wm)
    (hX : ∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) (w : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ x, GlobalTheory.LatVac.locCo co v (Xm x) = w := by
  set p : (κ → AF F) × (κ → AF F) := (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) with hp
  have hzat : At (evFin F v) (co.e.symm p) := by
    intro u hu
    have hp0 : u • p = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [← map_smul, hp0, map_zero]
  obtain ⟨x, hx⟩ := (hX _).1 hzat
  refine ⟨x, ?_⟩
  rw [hx]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · show evFin F v ((co.e (co.e.symm p)).1 k) = w.1 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
  · show evFin F v ((co.e (co.e.symm p)).2 k) = w.2 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)

theorem exists_locRho : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F _ _ v ψ hstd hunr Wm _ _ Bf κ _ co Y _ Xm χ hX hχ
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
    have h : Continuous (GlobalTheory.LatVac.liftV v) := by
      change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
      exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
    exact hstd.1.comp h
  have evFin_invOf_two : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  have hat : ∀ x, At (evFin F v) (Xm x) := fun x => (hX (Xm x)).2 ⟨x, rfl⟩
  refine ⟨fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc (GlobalTheory.LatVac.locCo co v (Xm x)), ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext; intro φ
    apply Subtype.ext; funext z
    simp [rhoSB, schr]
  · intro x y
    apply LinearMap.ext; intro φ
    apply Subtype.ext
    show schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm x))
        (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm y)) φ) =
      χ x y • schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm (x + y))) φ
    rw [schr_schr, map_add Xm, map_add (GlobalTheory.LatVac.locCo co v), ← hχ]
    congr 1
    rw [GlobalTheory.VacIndic.psi_of_at ψ (GlobalTheory.VacIndic.at_mul_left (GlobalTheory.LatVac.DualLoc.at_form co v (hat x) (Xm y))),
      map_mul (evFin F v), evFin_invOf_two, GlobalTheory.LatVac.DualLoc.evFin_form co v]
    rfl
  · intro x φ
    exact GlobalTheory.VacBridge.rho_acts_locCo co ψ v (Xm x) (hat x) φ
  · intro s hs
    rw [eq_top_iff]
    rintro t -
    have key := span_schr F v (GlobalTheory.LatVac.psiAt ψ v) (fun z => hunr z) κ s s.2
      (fun h => hs (Subtype.ext h)) t t.2
    have hmap : Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) =>
        schr (GlobalTheory.LatVac.psiAt ψ v) w (s : (κ → Fv F v) → ℂ)) =
        (Submodule.span ℂ (Set.range fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc
          (GlobalTheory.LatVac.locCo co v (Xm x)) s)).map (SB (κ → Fv F v)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨x, hx⟩ := locCo_onto v co Xm hX w
        exact ⟨x, by simp only [Function.comp_apply, Submodule.subtype_apply, rhoSB_apply, hx]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, rfl⟩
    rw [hmap] at key
    obtain ⟨u, hu, hut⟩ := key
    rwa [show u = t from Subtype.ext hut] at hu

end GlobalTheory.SchrLocModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_schroedinger_family_at_place : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  first | exact @GlobalTheory.SchrLocModel.exists_locRho | exact GlobalTheory.SchrLocModel.exists_locRho | (intros; apply GlobalTheory.SchrLocModel.exists_locRho <;> assumption)
end

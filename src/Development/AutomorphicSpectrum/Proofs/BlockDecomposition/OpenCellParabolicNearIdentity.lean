module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentity
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowD (i t : ℕ) (b : Fin (t + 1)) : Fin ((i + 1) + (t + 1) + 1) := Fin.castSucc (Fin.natAdd (i + 1) b)

theorem ePG_true_rowD (i t : ℕ) (b : Fin (t + 1)) : ePG (i + 1) (t + 1) ⟨true, b⟩ = rowD i t b :=
  Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])

def ent {n : ℕ} (a b : Fin (n + 1)) (p : Mir k n) : k :=
  ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b

theorem continuous_ent {n : ℕ} (a b : Fin (n + 1)) : Continuous (ent (k := k) a b) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b

theorem ent_last_last {n : ℕ} (p : Mir k n) : ent (Fin.last n) (Fin.last n) p = 1 := by
  have hh := (mem_Mir_iff k _).1 p.2
  show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1
  rw [hh]
  simp [eLast]

theorem colMat_mul_castSucc {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem continuous_colMat_append (i t : ℕ) :
    Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
  refine continuous_matrix fun a b => ?_
  by_cases hb : b = Fin.last _
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast a =>
      induction a using Fin.addCases with
      | left a => simpa [colMat] using continuous_const
      | right a =>
        have e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
            (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a := by
          intro d
          unfold colMat
          rw [if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]
        exact (continuous_apply a).congr fun d => (e d).symm
  · simpa [colMat, hb] using continuous_const

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_append i t)
  · exact continuous_const.sub (continuous_colMat_append i t)

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext a
    induction a using Fin.addCases <;> simp
  rw [this, colMat_zero, add_zero]

def delta (i t : ℕ) (u : Mir k ((i + 1) + (t + 1))) : Fin (t + 1) → k :=
  fun b => - ent (rowD i t b) (Fin.last _) u

theorem continuous_delta (i t : ℕ) : Continuous (delta (k := k) i t) :=
  continuous_pi fun b => (continuous_ent _ _).neg

theorem delta_one (i t : ℕ) : delta (k := k) i t 1 = 0 := by
  funext b
  have h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0 :=
    Matrix.one_apply_ne (Fin.castSucc_ne_last _)
  show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0
  rw [h0, neg_zero]

theorem eq_delta (i t : ℕ) (h u : Mir k ((i + 1) + (t + 1))) (hH : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (e : h = dEmb k i t d * u) : d = delta i t u := by
  funext b
  have hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hH
  have hz := mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_true_rowD, ePG_false_last] at hz
  have hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) *
        ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val := by
    rw [e]; rfl
  have hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (rowD i t b) (Fin.last _) = 0 := hz
  rw [hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc] at hz'
  have h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1 :=
    ent_last_last u
  rw [h1, mul_one, Fin.append_right] at hz'
  show d b = - ent (rowD i t b) (Fin.last _) u
  exact eq_neg_of_add_eq_zero_right hz'

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

open Small in
theorem h_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  intro k _ _ _ _ i t O hO
  let w : Mir k ((i + 1) + (t + 1)) := wEl k i t
  let f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1)) :=
    fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)
  have hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹ :=
    (continuous_const.mul continuous_inv).mul continuous_const
  have hf : Continuous f :=
    ((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu
  have f1 : f 1 = 1 := by
    have e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1 := by group
    show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1
    rw [e, delta_one, dEmb_zero, one_mul]
  refine ⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩
  intro h hH d x hx e
  have e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by
    have e2 : dEmb k i t d * w = h * w * x := e
    calc h = (h * w * x) * x⁻¹ * w⁻¹ := by group
      _ = (dEmb k i t d * w) * x⁻¹ * w⁻¹ := by rw [e2]
      _ = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by group
  have hd := eq_delta i t h _ hH d e'
  have hfx : f x = h := by
    show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h
    rw [← hd, ← e']
  have : f x ∈ O := hx
  rwa [hfx] at this

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentityStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_parabolic_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.h_small | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.h_small | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.h_small <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwiner
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwiner
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem cIndSpace_apply_mem_mul {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] {H : Subgroup G}
    {σ : Representation ℂ H W} (f : GlobalTheory.PRep.cIndSpace H σ) (h : G) (hh : h ∈ H)
    (g : G) : f.1.1.1 (h * g) = σ ⟨h, hh⟩ (f.1.1.1 g) := by
  exact f.1.1.2 ⟨h, hh⟩ g

private theorem isHK_empty {G : Type} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H ∅ := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK
  exact ⟨fun _ _ _ => Iff.rfl, ⊤, by simp, fun _ _ _ => Iff.rfl⟩

private theorem isHK_union {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A ∪ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_union, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_union, hA₂ g x hx.1, hB₂ g x hx.2]

private theorem isHK_diff {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A \ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_diff, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_diff, hA₂ g x hx.1, hB₂ g x hx.2]

theorem exists_cInd_restrict_eq {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W') (hι : Continuous ι) (hσ : IsSmooth σ) (hsurj : Function.Surjective q)
    (hH : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (F : cIndSpace H' σ') : ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  classical
  obtain ⟨C, hC, hsupp⟩ : ∃ C : Set G', IsCompact C ∧
      ∀ g, F.1.1.1 g ≠ 0 → ∃ h ∈ H', ∃ c ∈ C, g = h * c := F.2
  have hloc : ∀ c : G', ∃ T : Set G, ∃ U ∈ 𝓝 c, GlobalTheory.CompanionTheory.LeibPhi.IsHK H T ∧
      (∀ y ∈ U, ι y ∈ T) ∧ ∃ e : GlobalTheory.PRep.cIndSpace H σ,
        ∀ x, ι x ∈ T → q (e.1.1.1 (ι x)) = F.1.1.1 x := by
    intro c
    obtain ⟨K', hK'o, hK'⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H' σ' F
    obtain ⟨w, hw⟩ := hsurj (F.1.1.1 c)
    obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_value H σ hσ hbase (ι c) w
    obtain ⟨Ke, hKeo, hKe⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H σ e
    have hS : {y : G' | c⁻¹ * y * c ∈ K' ∧ ι (c⁻¹ * y * c) ∈ Ke} ∈ 𝓝 (1 : G') := by
      have hcont : Continuous (fun y : G' => c⁻¹ * y * c) := by fun_prop
      have hopen : IsOpen {z : G' | z ∈ K' ∧ ι z ∈ Ke} := hK'o.inter (hKeo.preimage hι)
      exact (hopen.preimage hcont).mem_nhds (by simp [one_mem])
    obtain ⟨K, hK, hKemb⟩ := hemb _ hS
    have hconj : (fun μ : G => ι c * μ * (ι c)⁻¹) ⁻¹' K ∈ 𝓝 (1 : G) := by
      have hcont : Continuous (fun μ : G => ι c * μ * (ι c)⁻¹) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    obtain ⟨M, hMo, -, hMsub⟩ := hbase _ hconj
    refine ⟨{g | ∃ a ∈ H, ∃ x ∈ M, g = a * ι c * x}, {y | ι (c⁻¹ * y) ∈ M}, ?_,
      GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H M hMo (ι c), ?_, e, ?_⟩
    · have hcont : Continuous (fun y : G' => ι (c⁻¹ * y)) := hι.comp (continuous_const_mul c⁻¹)
      exact (hMo.preimage hcont).mem_nhds (by simp [one_mem])
    · intro y hy
      exact ⟨1, one_mem _, ι (c⁻¹ * y), hy, by simp⟩
    · rintro x ⟨a, ha, μ, hμ, hx⟩
      have hκ : ι c * μ * (ι c)⁻¹ ∈ K := hMsub hμ
      obtain ⟨h', hh', κ', hκ', hxeq⟩ := hKemb (x * c⁻¹) a ha (ι c * μ * (ι c)⁻¹) hκ
        (by rw [map_mul, hx, map_inv]; group)
      have hx' : x = h' * (c * (c⁻¹ * κ' * c)) := by
        have h0 : x = x * c⁻¹ * c := by group
        rw [h0, hxeq]
        group
      have hι' : ι h' ∈ H := (hH h').1 hh'
      have hFx : F.1.1.1 x = σ' ⟨h', hh'⟩ (q w) := by
        rw [hx', cIndSpace_apply_mem_mul F h' hh', hK' c _ hκ'.1, hw]
      rw [hFx, hx', map_mul, map_mul, cIndSpace_apply_mem_mul e _ hι',
        hKe _ _ hκ'.2, he]
      exact hq ⟨h', hh'⟩ hι' w
  choose T U hU hT hUT e he using hloc
  obtain ⟨t, -, hCt⟩ := hC.elim_nhds_subcover U (fun c _ => hU c)
  have hglue : ∀ s : Finset G', ∃ V : Set G, GlobalTheory.CompanionTheory.LeibPhi.IsHK H V ∧
      (∀ c ∈ s, T c ⊆ V) ∧ ∃ f : GlobalTheory.PRep.cIndSpace H σ,
        (∀ g ∉ V, f.1.1.1 g = 0) ∧ ∀ x, ι x ∈ V → q (f.1.1.1 (ι x)) = F.1.1.1 x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨∅, isHK_empty H, by simp, 0, fun g _ => ?_, fun x hx => ?_⟩
      · rfl
      · simp at hx
    | @insert c s hcs ih =>
      obtain ⟨V, hV, hsV, f, hf0, hf⟩ := ih
      obtain ⟨f', hf'in, hf'out⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H σ
        (isHK_diff (hT c) hV) (e c)
      have hadd : ∀ g, (f + f').1.1.1 g = f.1.1.1 g + f'.1.1.1 g := fun _ => rfl
      refine ⟨V ∪ T c, isHK_union hV (hT c), ?_, f + f', ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Set.subset_union_right
        · exact (hsV d hd).trans Set.subset_union_left
      · intro g hg
        rw [Set.mem_union, not_or] at hg
        rw [hadd, hf0 g hg.1, hf'out g (fun h => hg.2 h.1), add_zero]
      · intro x hx
        by_cases hxV : ι x ∈ V
        · rw [hadd, hf'out _ (fun h => h.2 hxV), add_zero]
          exact hf x hxV
        · rcases hx with hx | hx
          · exact absurd hx hxV
          · rw [hadd, hf0 _ hxV, hf'in _ ⟨hx, hxV⟩, zero_add]
            exact he c x hx
  obtain ⟨V, hV, htV, f, hf0, hf⟩ := hglue t
  refine ⟨f, fun x => ?_⟩
  by_cases hx : ι x ∈ V
  · exact (hf x hx).symm
  · rw [hf0 _ hx, map_zero]
    by_contra hne
    obtain ⟨h', hh', c', hc', rfl⟩ := hsupp x hne
    obtain ⟨d, hd, hc'U⟩ := Set.mem_iUnion₂.1 (hCt hc')
    have hmem : ι c' ∈ V := htV d hd (hUT d c' hc'U)
    unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at hV
    apply hx
    rw [map_mul]
    exact (hV.1 _ ((hH h').1 hh') _).2 hmem

end GlobalTheory.CompanionTheory.LeibPhi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwinerStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_map_induced_surjective_intertwiner : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → IsSmooth σ → Function.Surjective q →
    (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ F : cIndSpace H' σ', ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | exact GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeMaxEvenAlmostAll
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := rfl

theorem hR_apply (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x y = ∑ i, ∑ j, sigR (Fv F v) σ (x i) * inclR (Fv F v) (J i j) * y j := rfl

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_hR (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  rw [hR_apply, hR_apply, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sigR_sigR hσ, sigR_inclR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ i j]
  ring

theorem hR_mem (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) {x y : Fin n → Fv F v ⊗[F] E}
    (hx : ∀ i, x i ∈ intLoc F E v) (hy : ∀ i, y i ∈ intLoc F E v) : hR (Fv F v) σ J x y ∈ intLoc F E v := by
  rw [hR_apply]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (sigR_mem_intLoc σ (hx i)) (hJv i j)) (hy j)

theorem hR_single (i : Fin n) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (Pi.single i 1) z = (J.map (inclR (F := F) (Fv F v)) *ᵥ z) i := by
  rw [hR_apply, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem mem_of_hR_single (hdet : J.det ≠ 0) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : ∀ i, hR (Fv F v) σ J (Pi.single i 1) z ∈ intLoc F E v) (a : Fin n) :
    z a ∈ intLoc F E v := by
  have e : J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _) (map_one _)]
  have hz' : z = J⁻¹.map (inclR (F := F) (Fv F v)) *ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, w = J.map (inclR (F := F) (Fv F v)) *ᵥ z := ⟨_, rfl⟩
  have hw' : ∀ j, w j ∈ intLoc F E v := fun j => by rw [hw, ← hR_single (σ := σ)]; exact hz j
  rw [← hw] at hz'
  rw [hz']
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hJi a j) (hw' j)

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem single_mem_latLoc_std (i : Fin n) :
    (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E n) v := by
  refine mem_latLoc_stdLattice.2 fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem sum_single_smul (y : Fin n → Fv F v ⊗[F] E) : ∑ i, y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem isLat_latLoc_std : IsLat (intLoc F E v) (latLoc F (stdLattice E n) v) := by
  constructor
  · refine Submodule.fg_def.2 ⟨Set.range fun i => (Pi.single i 1 : Fin n → Fv F v ⊗[F] E), Set.finite_range _,
      le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact single_mem_latLoc_std i
    · intro y hy
      have h := mem_latLoc_stdLattice.1 hy
      rw [← sum_single_smul y]
      refine sum_mem fun i _ => ?_
      have : y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) =
          (⟨y i, h i⟩ : intLoc F E v) • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [eq_top_iff]
    intro y _
    rw [← sum_single_smul y]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_latLoc_std i))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem hR_self_eq (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x x = inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x +
      sigR (Fv F v) σ (inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x) := by
  have hs : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [map_mul, sigR_hR hσ hJ, sigR_inclR, hs, ← add_mul, ← map_add (f := _)]
  have : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  rw [this, map_one, one_mul]

theorem isMaxEven_isAdapted_std (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    (h2 : inclR (Fv F v) (2⁻¹ : E) ∈ intLoc F E v) {r : ℕ} (x y : Fin r → Fin n → Fv F v ⊗[F] E)
    (hx : ∀ i a, x i a ∈ intLoc F E v) (hy : ∀ i a, y i a ∈ intLoc F E v) :
    IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F (stdLattice E n) v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) x y (latLoc F (stdLattice E n) v) := by
  have hint : ∀ a ∈ latLoc F (stdLattice E n) v, ∀ b ∈ latLoc F (stdLattice E n) v,
      hR (Fv F v) σ J a b ∈ intLoc F E v := fun a ha b hb =>
    hR_mem hJv (mem_latLoc_stdLattice.1 ha) (mem_latLoc_stdLattice.1 hb)
  refine ⟨⟨isLat_latLoc_std, ⟨hint, fun a ha => ⟨_, mul_mem h2 (hint a ha a ha), hR_self_eq hσ hJ.1 a⟩⟩, ?_⟩, ?_⟩
  · intro L' hL' hle z hz
    refine mem_latLoc_stdLattice.2 (mem_of_hR_single (σ := σ) hJ.2 hJi fun i => ?_)
    exact hL'.1 _ (hle (single_mem_latLoc_std i)) _ hz
  · intro z
    simp only [mem_latLoc_stdLattice]
    have hc : ∀ (c d : Fin r → Fv F v ⊗[F] E) (a : Fin n),
        (z - ∑ i, c i • x i - ∑ i, d i • y i) a = z a - ∑ i, c i * x i a - ∑ i, d i * y i a := by
      intro c d a
      simp [Finset.sum_apply]
    constructor
    · intro hz
      have h1 : ∀ i, hR (Fv F v) σ J (x i) z ∈ intLoc F E v := fun i => hR_mem hJv (hx i) hz
      have h3 : ∀ i, hR (Fv F v) σ J (y i) z ∈ intLoc F E v := fun i => hR_mem hJv (hy i) hz
      refine ⟨h1, h3, fun a => ?_⟩
      rw [hc]
      exact sub_mem (sub_mem (hz a) (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))
    · rintro ⟨h1, h3, hw⟩ a
      have := hw a
      rw [hc] at this
      have e : z a = (z a - ∑ i, hR (Fv F v) σ J (y i) z * x i a - ∑ i, hR (Fv F v) σ J (x i) z * y i a) +
          ∑ i, hR (Fv F v) σ J (y i) z * x i a + ∑ i, hR (Fv F v) σ J (x i) z * y i a := by ring
      rw [e]
      exact add_mem (add_mem this (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

theorem exists_lattice_maxEven_adapted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ _hW
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  refine ⟨stdLattice E n, isLattice_stdLattice.toIsLattice, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
    eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
    with v h1 h2 h3 h4 h5
  exact isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5

end GlobalTheory.CompanionTheory.KFin.AE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicator
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirLevi.Bump

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

def IntM (m : GL (Fin n) k) : Prop :=
  ∀ i, Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i) ∈ polyBall (k := k) n 1

theorem intM_one : IntM (1 : GL (Fin n) k) := by
  intro i j
  show valuation k (((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ((1 : kˣ) : k)
  by_cases h : i = j
  · simp [h]
  · simp [one_apply, h]

theorem IntM.mulVec_mem {m : GL (Fin n) k} (hm : IntM m) {s : kˣ} {v : Fin n → k}
    (hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s) :
    Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v) ∈ polyBall (k := k) n s :=
  fun i => dotProduct_mem_cball (a := 1) (b := s) (c := s) (by simp) (hm i) hv

theorem isOpen_intM : IsOpen {m : GL (Fin n) k | IntM m} := by
  have h : {m : GL (Fin n) k | IntM m} = ⋂ i, (fun m : GL (Fin n) k =>
      Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i)) ⁻¹'
        (polyBall (k := k) n 1 : Set (Multiplicative (Fin n → k))) := by
    ext m
    simp [IntM]
  rw [h]
  refine isOpen_iInter_of_finite fun i => (isOpen_polyBall n 1).preimage ?_
  exact continuous_ofAdd.comp (continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem continuous_colv : Continuous (colv : Mir k n → Fin n → k) :=
  continuous_pi fun i => (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)

theorem continuous_mvec : Continuous (mvec : Mir k n → Fin n → k) := by
  have h1 : Continuous fun x : Mir k n =>
      (((mirabolicProjection k n x)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val.comp (continuous_inv.comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n))
  exact h1.matrix_mulVec continuous_colv

theorem continuous_lv : Continuous (lv k n) :=
  continuous_induced_rng.2 (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n)

def bumpF (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E) (g : Mir k n) : E :=
  @ite _ (Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s) (Classical.propDecidable _)
    (ρ (lv k n (mirabolicProjection k n g)) e) 0

variable (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E)

theorem bumpF_levi_mul (m : GL (Fin n) k) (g : Mir k n) :
    bumpF ρ s e (levi k n m * g) = ρ (lv k n m) (bumpF ρ s e g) := by
  unfold bumpF
  rw [mvec_levi_mul, map_mul, mirProj_levi, map_mul, map_mul, Module.End.mul_apply]
  split_ifs <;> simp

theorem bumpF_equi (h : LH k n) (g : Mir k n) :
    bumpF ρ s e ((h : Mir k n) * g) = ρ h (bumpF ρ s e g) := by
  obtain ⟨m, hm⟩ := h.2
  have e1 : h = lv k n m := Subtype.ext hm.symm
  rw [e1]
  exact bumpF_levi_mul ρ s e m g

theorem bumpF_levi_uv (q : GL (Fin n) k) (w : Fin n → k) :
    bumpF ρ s e (levi k n q * uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _)
        (ρ (lv k n q) e) 0 := by
  unfold bumpF
  rw [mvec_levi_mul_uv, map_mul, mirProj_levi, mirProj_uv, mul_one]

theorem bumpF_uv (w : Fin n → k) :
    bumpF ρ s e (uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  have h := bumpF_levi_uv ρ s e 1 w
  rw [map_one (levi k n), one_mul, map_one (lv k n), map_one ρ] at h
  simpa using h

theorem mul_formula (p m : GL (Fin n) k) (v a : Fin n → k) :
    (levi k n p * uv n v) * (levi k n m * uv n a) = levi k n (p * m) *
      uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) := by
  rw [uv_add, map_mul, mul_assoc (levi k n p), ← mul_assoc (uv n v), uv_mul_levi]
  simp only [mul_assoc]

theorem bumpF_fix (p m : GL (Fin n) k) (v a : Fin n → k) (h1 : IntM m) (h2 : IntM m⁻¹)
    (hm : ρ (lv k n m) e = e) (ha : Multiplicative.ofAdd a ∈ polyBall (k := k) n s) :
    bumpF ρ s e ((levi k n p * uv n v) * (levi k n m * uv n a)) = bumpF ρ s e (levi k n p * uv n v) := by
  rw [mul_formula, bumpF_levi_uv, bumpF_levi_uv, map_mul, map_mul, Module.End.mul_apply, hm]
  have hiff : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) ∈
      polyBall (k := k) n s ↔ Multiplicative.ofAdd v ∈ polyBall (k := k) n s := by
    constructor
    · intro h
      have h3 : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) ∈
          polyBall (k := k) n s := by
        have h4 := mul_mem h (inv_mem ha)
        rwa [ofAdd_add, mul_inv_cancel_right] at h4
      have h5 := h1.mulVec_mem h3
      rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h5
    · intro h
      rw [ofAdd_add]
      exact mul_mem (h2.mulVec_mem h) ha
  by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s
  · rw [if_pos hv, if_pos (hiff.2 hv)]
  · rw [if_neg hv, if_neg (fun c => hv (hiff.1 c))]

def nbhd : Set (Mir k n) :=
  {x | IntM (mirabolicProjection k n x) ∧ IntM (mirabolicProjection k n x)⁻¹ ∧ ρ (lv k n (mirabolicProjection k n x)) e = e ∧
    Multiplicative.ofAdd (mvec x) ∈ polyBall (k := k) n s}

theorem isOpen_nbhd (hρ : IsSmooth ρ) : IsOpen (nbhd ρ s e) := by
  unfold nbhd
  have hp := GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n
  exact (isOpen_intM.preimage hp).inter ((isOpen_intM.preimage (continuous_inv.comp hp)).inter
    (((hρ e).preimage (continuous_lv.comp hp)).inter
      ((isOpen_polyBall n s).preimage (continuous_ofAdd.comp continuous_mvec))))

theorem one_mem_nbhd : (1 : Mir k n) ∈ nbhd ρ s e := by
  have hm : mvec (1 : Mir k n) = 0 := by
    have h := mvec_uv (k := k) n 0
    rwa [uv_zero] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one]; exact intM_one
  · rw [map_one, inv_one]; exact intM_one
  · simp
  · rw [hm]; exact one_mem _

theorem bumpF_mul_nbhd (g x : Mir k n) (hx : x ∈ nbhd ρ s e) :
    bumpF ρ s e (g * x) = bumpF ρ s e g := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have h := bumpF_fix ρ s e (mirabolicProjection k n g) (mirabolicProjection k n x) (mvec g) (mvec x) h1 h2 h3 h4
  rwa [← decomp g, ← decomp x] at h

theorem bumpF_mem : bumpF ρ s e ∈ indSpace (LH k n) ρ := fun h g => bumpF_equi ρ s e h g

theorem bumpF_smooth (hρ : IsSmooth ρ) :
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) ∈ smoothPart (ind (LH k n) ρ) := by
  have hfix : nbhd ρ s e ⊆ (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
      (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) : Set (Mir k n)) := by
    intro x hx
    apply Subtype.ext
    funext g
    exact bumpF_mul_nbhd ρ s e g x hx
  exact (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ)).isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset ((isOpen_nbhd ρ s e hρ).mem_nhds (one_mem_nbhd ρ s e)) hfix)

theorem bumpF_support : ∃ C : Set (Mir k n), IsCompact C ∧ ∀ g, bumpF ρ s e g ≠ 0 →
    ∃ h ∈ LH k n, ∃ c ∈ C, g = h * c := by
  refine ⟨unipIn k n '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))),
    (isCompact_polyBall n s).image (continuous_unipIn n), fun g hg => ?_⟩
  have hL : Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s := by
    by_contra hc
    exact hg (if_neg hc)
  exact ⟨levi k n (mirabolicProjection k n g), ⟨_, rfl⟩, uv n (mvec g), ⟨_, hL, rfl⟩, decomp g⟩

theorem exists_bump_restr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E),
    ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v =
      @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  intro k _ _ _ _ n E _ _ ρ hρ s e
  exact ⟨⟨⟨⟨bumpF ρ s e, bumpF_mem ρ s e⟩, bumpF_smooth ρ s e hρ⟩, bumpF_support ρ s e⟩,
    fun v => bumpF_uv ρ s e v⟩

end GlobalTheory.CompanionTheory.MirLevi.Bump

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicatorStatement
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_ball_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E), ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | exact GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | (intros; apply GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr <;> assumption)
end
end

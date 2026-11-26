module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonReps

def RepsIn {G : Type} [AddCommGroup G] (X Y : AddSubgroup G) (S : Finset G) : Prop :=
  (∀ x ∈ S, x ∈ Y) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ X → x = y) ∧ ∀ y ∈ Y, ∃ x ∈ S, y - x ∈ X

theorem isReps_map {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] [DecidableEq V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {S : Finset G} (h : RepsIn X Y S) :
    IsReps (X.map f) (Y.map f) (S.image f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨x, h1 x hx, rfl⟩
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨m, hm, hme⟩ := hvw
    rw [← map_sub] at hme
    rw [h2 x hx y hy (hf hme ▸ hm)]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := h3 y hy
    exact ⟨f x, Finset.mem_image_of_mem f hx, ⟨y - x, hyx, map_sub f y x⟩⟩

theorem repsIn_preimage {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {T : Finset V} (h : IsReps (X.map f) (Y.map f) T) :
    RepsIn X Y (T.preimage f hf.injOn) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := h1 (f x) (Finset.mem_preimage.1 hx)
    exact hf hyx ▸ hy
  · intro x hx y hy hxy
    exact hf (h2 _ (Finset.mem_preimage.1 hx) _ (Finset.mem_preimage.1 hy) ⟨x - y, hxy, map_sub f x y⟩)
  · intro y hy
    obtain ⟨v, hv, hyv⟩ := h3 (f y) ⟨y, hy, rfl⟩
    obtain ⟨x, -, rfl⟩ := h1 v hv
    refine ⟨x, Finset.mem_preimage.2 hv, ?_⟩
    obtain ⟨m, hm, hme⟩ := hyv
    rw [← map_sub] at hme
    exact hf hme ▸ hm

theorem repsIn_move {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] [DecidableEq G]
    (X Y X₀ Y₀ : Submodule R G) (g c k : R) (hg : g = 1 + c * k)
    (hY : ∀ y ∈ Y, g • y ∈ Y₀) (hY₀ : ∀ y ∈ Y₀, g • y ∈ Y) (hX : ∀ x ∈ X, g • x ∈ X₀) (hX₀ : ∀ x ∈ X₀, g • x ∈ X)
    (hcY : ∀ y ∈ Y, c • y ∈ X) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀) {S₀ : Finset G}
    (hS : RepsIn X₀.toAddSubgroup Y₀.toAddSubgroup S₀) :
    RepsIn X.toAddSubgroup Y.toAddSubgroup (S₀.image (g • ·)) := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hgg : ∀ z : G, z = g • g • z - (2 * k + c * k * k) • (c • z) := by
    intro z
    rw [smul_smul, smul_smul, ← sub_smul, hg]
    have : (1 + c * k) * (1 + c * k) - (2 * k + c * k * k) * c = 1 := by ring
    rw [this, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact hY₀ x (h1 x hx)
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    have hxy : x - y ∈ Y₀ := Y₀.sub_mem (h1 x hx) (h1 y hy)
    have e1 : g • g • (x - y) ∈ X₀ := by
      rw [smul_sub g x y]; exact hX _ hvw
    have e2 : x - y ∈ X₀ := by
      rw [hgg (x - y)]
      exact X₀.sub_mem e1 (X₀.smul_mem _ (hcY₀ _ hxy))
    rw [h2 x hx y hy e2]
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := h3 (g • y) (hY y hy)
    refine ⟨g • x, Finset.mem_image_of_mem _ hx, ?_⟩
    have e : y - g • x = g • (g • y - x) - (2 * k + c * k * k) • (c • y) := by
      conv_lhs => rw [hgg y]
      rw [smul_sub]; abel
    rw [e]
    exact X.sub_mem (hX₀ _ hyx) (X.smul_mem _ (hcY y hy))

theorem common_reps_of {R G V κ : Type} [CommRing R] [AddCommGroup G] [Module R G] [AddCommGroup V] [Module ℂ V]
    (f : G →+ V) (hf : Function.Injective f) (g c k : R) (hg : g = 1 + c * k)
    (X Y : κ → Submodule R G) (X₀ Y₀ : Submodule R G)
    (hY : ∀ i, ∀ y ∈ Y i, g • y ∈ Y₀) (hY₀ : ∀ i, ∀ y ∈ Y₀, g • y ∈ Y i) (hX : ∀ i, ∀ x ∈ X i, g • x ∈ X₀)
    (hX₀ : ∀ i, ∀ x ∈ X₀, g • x ∈ X i) (hcY : ∀ i, ∀ y ∈ Y i, c • y ∈ X i) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀)
    (hidx : relIdx (X₀.toAddSubgroup.map f) (Y₀.toAddSubgroup.map f) ≠ 0) :
    ∃ S : Finset V, ∀ i, IsReps ((X i).toAddSubgroup.map f) ((Y i).toAddSubgroup.map f) S := by
  classical
  have h0 := repsIn_preimage f hf (Formalism.L2.Ker.repsOf_spec _ _ hidx)
  exact ⟨(((Formalism.L2.Ker.repsOf _ _).preimage f hf.injOn).image (g • ·)).image f, fun i =>
    isReps_map f hf (repsIn_move (X i) (Y i) X₀ Y₀ g c k hg (hY i) (hY₀ i) (hX i) (hX₀ i) (hcY i) hcY₀ h0)⟩

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem smul_mem_twO_of (M M₀ : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (g : 𝓞 E)
    (hg : ∀ x ∈ M, g • x ∈ M₀) {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ M c e) : g • x ∈ Formalism.L2.Ker.twist₂ M₀ c e := by
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨s, hs, hsx⟩ := hx Q
  refine ⟨s, hs, ?_⟩
  rw [smul_comm _ g, smul_comm s g]
  exact hg _ hsx

theorem natsmul_mem_twO (L : Submodule (𝓞 E) W) (c : ℕ) (e e' : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e' Q ≤ e Q + 1)
    {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ L c e) : (c : 𝓞 E) • x ∈ Formalism.L2.Ker.twist₂ L c e' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e Q + 1 - e' Q := ⟨(e Q + 1 - e' Q).toNat, Int.toNat_of_nonneg (by linarith [he Q])⟩
  have key : ((c : E) ^ e' Q)⁻¹ • ((c : 𝓞 E) • x) = ((c : 𝓞 E) ^ n) • (((c : E) ^ e Q)⁻¹ • x) := by
    rw [← IsScalarTower.algebraMap_smul E ((c : 𝓞 E) ^ n), ← IsScalarTower.algebraMap_smul E (c : 𝓞 E) x, smul_smul, smul_smul]
    congr 1
    simp only [map_pow, map_natCast]
    rw [← zpow_neg, ← zpow_neg, ← zpow_natCast, hn, ← zpow_add_one₀ hcE, ← zpow_add₀ hcE]
    congr 1; ring
  rw [key]
  exact Submodule.smul_mem _ _ (hx Q)

theorem mem_twO_zero (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) : x ∈ Formalism.L2.Ker.twist₂ M c (fun _ => 0) ↔ x ∈ M := by
  rw [Formalism.L2.Ker.mem_twO]
  simp only [zpow_zero, inv_one, one_smul]
  exact ⟨fun h => Formalism.L2.Ker.mem_of_forall_locP M h, fun h Q => Formalism.L2.Ker.le_locP' M Q h⟩

end Tw

end GlobalTheory.CommonReps

namespace GlobalTheory.CommonReps

theorem common_reps_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  intro E _ _ _ ι κ _ _ _ a b emb δ AA0 SS cl N₀ N₀' N N' g hδ hk hmv h1 h2 h3
  obtain ⟨k, hk⟩ := hk
  set f : Formalism.L2.Col.HomE E a b →+ VV ι a b := embH emb δ with hfdef
  have hf : Function.Injective f := embH_inj emb hδ
  have hinf : ∀ M A : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b),
      M.toAddSubgroup.map f ⊓ A.toAddSubgroup.map f = (M ⊓ A).toAddSubgroup.map f := fun M A =>
    (AddSubgroup.map_inf_eq M.toAddSubgroup A.toAddSubgroup f hf).symm
  have hexpS : ∀ Q, expS SS Q ≤ 1 ∧ -1 ≤ expS SS Q := fun Q => by
    rcases Formalism.L2.Ker.expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num

  have hcA : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfAO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).1]) hy)
  have hcB : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfBO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).2]) hy)
  have hcM : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ M, (cl : 𝓞 E) • y ∈ halfBO SS M cl := fun M y hy =>
    natsmul_mem_twO M cl (fun _ => 0) _ (fun Q => by linarith [(hexpS Q).1]) ((mem_twO_zero M cl y).2 hy)
  have hA : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfAO SS M cl, g • y ∈ halfAO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  have hB : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfBO SS M cl, g • y ∈ halfBO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  obtain ⟨SX, hSX⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfAO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i => hA _ _ (hmv i).1) (fun i => hA _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcA _) (hcA _) h1
  have h2' := h2
  simp only [LamC, AC, BC, laV] at h2'
  rw [hinf] at h2'
  obtain ⟨SA, hSA⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl)
    (fun i => perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl) (halfBO SS (perO AA0 N₀ N₀') cl)
    (perO AA0 N₀ N₀' ⊓ halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i y hy => ⟨(hmv i).1 _ hy.1, hA _ _ (hmv i).1 _ hy.2⟩) (fun i y hy => ⟨(hmv i).2 _ hy.1, hA _ _ (hmv i).2 _ hy.2⟩)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2)
    (fun i y hy => hcM _ y hy.1) (fun y hy => hcM _ y hy.1) h2'
  obtain ⟨SB, hSB⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfBO SS (perO AA0 N₀ N₀') cl)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcB _) (hcB _) h3
  refine ⟨SX, SA, SB, fun i => ⟨hSX i, ?_, hSB i⟩⟩
  have e : LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl =
      (perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl).toAddSubgroup.map f := hinf _ _
  rw [e]
  exact hSA i

end GlobalTheory.CommonReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalvesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.common_representatives_period_lattice_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  first | exact @GlobalTheory.CommonReps.common_reps_halves | exact GlobalTheory.CommonReps.common_reps_halves | (intros; apply GlobalTheory.CommonReps.common_reps_halves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacua
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem comb_of_scalar {X A M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s) (cA : A →₀ ℂ) :
    ∃ C : X →₀ ℂ, ∀ s, vac s → (cA.sum fun p z => z • a p s) = C.sum fun x z => z • r x s := by
  choose ca hca using ha
  refine ⟨Finsupp.linearCombination ℂ ca cA, fun s hs => ?_⟩
  have h : Finsupp.linearCombination ℂ (fun x => r x s) (Finsupp.linearCombination ℂ ca cA) =
      Finsupp.linearCombination ℂ (fun p => a p s) cA := by
    rw [LinearMap.map_finsupp_linearCombination]
    congr 2
    funext p
    exact (Finsupp.linearCombination_apply ℂ (ca p)).trans (hca p s hs).symm
  calc (cA.sum fun p z => z • a p s) = Finsupp.linearCombination ℂ (fun p => a p s) cA :=
        (Finsupp.linearCombination_apply ℂ cA).symm
    _ = _ := h.symm
    _ = _ := Finsupp.linearCombination_apply ℂ _

theorem comb_transfer {X A B M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (b : B → Module.End ℂ M)
    (hmodel : ∀ c : X →₀ ℂ, ∀ s, s ≠ 0 → vac s → (c.sum fun x z => z • r x s) = 0 →
      ∀ s', vac s' → (c.sum fun x z => z • r x s') = 0)
    (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s)
    (hb : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → b p s = c.sum fun x z => z • r x s)
    (cA : A →₀ ℂ) (cB : B →₀ ℂ) (s0 : M) (h0 : s0 ≠ 0) (hv : vac s0)
    (heq : (cA.sum fun p z => z • a p s0) = cB.sum fun p z => z • b p s0) :
    ∀ s, vac s → (cA.sum fun p z => z • a p s) = cB.sum fun p z => z • b p s := by
  obtain ⟨CA, hA⟩ := comb_of_scalar vac r a ha cA
  obtain ⟨CB, hB⟩ := comb_of_scalar vac r b hb cB
  have hsub : ∀ s, ((CA - CB).sum fun x z => z • r x s) =
      (CA.sum fun x z => z • r x s) - CB.sum fun x z => z • r x s := by
    intro s
    have e : ∀ C : X →₀ ℂ, (C.sum fun x z => z • r x s) = Finsupp.linearCombination ℂ (fun x => r x s) C :=
      fun C => (Finsupp.linearCombination_apply ℂ C).symm
    rw [e, e, e, map_sub]
  have h0' : ((CA - CB).sum fun x z => z • r x s0) = 0 := by
    rw [hsub, ← hA _ hv, ← hB _ hv, heq, sub_self]
  intro s hs
  have h := hmodel (CA - CB) s0 h0 hv h0' s hs
  rw [hsub, sub_eq_zero, ← hA s hs, ← hB s hs] at h
  exact h

theorem howe_on_span (hH : HoweUnram) {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ}
    {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}
    (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (s0 : M) (h0 : s0 ≠ 0) (hv : LocVac ρ s0) :
    (∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
        (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun h => ω (1, h) s0)) ∧
    ∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun g => ω (g, 1) s0) := by
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  set M0 := Submodule.span ℂ (Set.range fun x => ρ x s0) with hM0
  have hs0 : s0 ∈ M0 := by
    refine Submodule.subset_span ⟨0, ?_⟩
    simp [hp.rho_zero]
  have hρ : ∀ x, ∀ m ∈ M0, ρ x m ∈ M0 := by
    intro x m hm
    have hle : M0 ≤ M0.comap (ρ x) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ρ x (ρ y s0) = (ρ x * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.rho_mul x y]
      exact M0.smul_mem _ (Submodule.subset_span ⟨x + y, rfl⟩)
    exact hle hm
  have hω : ∀ p, ∀ m ∈ M0, ω p m ∈ M0 := by
    rintro ⟨g, h⟩ m hm
    have hle : M0 ≤ M0.comap (ω (g, h)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ω (g, h) (ρ y s0) = (ω (g, h) * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.norm g h y]
      refine hρ _ _ ?_
      obtain ⟨c, hc⟩ := scal (g, h)
      rw [hc s0 hv]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨c, rfl⟩
    exact hle hm
  let ρ0 : Matrix (Fin n') (Fin n) L → Module.End ℂ M0 := fun x => (ρ x).restrict (hρ x)
  let ω0 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M0 :=
    { toFun := fun p => (ω p).restrict (hω p)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro p p'
        ext m
        simp }
  have ρ0_val : ∀ x (m : M0), ((ρ0 x m : M0) : M) = ρ x m := fun _ _ => rfl
  have ω0_val : ∀ p (m : M0), ((ω0 p m : M0) : M) = ω p m := fun _ _ => rfl
  let t0 : M0 := ⟨s0, hs0⟩
  have hv0 : LocVac ρ0 t0 := fun u hu => Subtype.ext (hv u hu)
  have ht0 : t0 ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hspan : Submodule.span ℂ (Set.range fun x => ρ0 x t0) = ⊤ := by
    have e : (Set.range fun x => ρ0 x t0) = (Subtype.val ⁻¹' (Set.range fun x => ρ x s0) : Set M0) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hp0 : LocPair ϖ σ q δ JS JT ψ ρ0 ω0 :=
    { unr := hp.unr
      odd := hp.odd
      intS := hp.intS
      intT := hp.intT
      hermS := hp.hermS
      hermT := hp.hermT
      delta := hp.delta
      psi_int := hp.psi_int
      psi_ne := hp.psi_ne
      rho_zero := by
        ext m
        simp [ρ0, hp.rho_zero]
      rho_mul := by
        intro x y
        ext m
        have h := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.rho_mul x y)
        exact h
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, t0, hv0, rfl⟩
      norm := by
        intro g h x
        ext m
        have e := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.norm g h x)
        exact e
      fix := by
        intro g h hg hh s hs
        exact Subtype.ext (hp.fix g h hg hh s (fun u hu => congrArg Subtype.val (hs u hu))) }
  obtain ⟨h1, h2⟩ := hH L ϖ σ q δ n n' JS JT ψ M0 ρ0 ω0 hp0 t0 ht0 hv0 hspan
  constructor
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h1 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h2 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h

theorem howe_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  intro hH L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  have model := GlobalTheory.T.locPair_vacuum_relation_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  by_cases hz : ∃ s0 : M, s0 ≠ 0 ∧ LocVac ρ s0
  · obtain ⟨s0, h0, hv⟩ := hz
    obtain ⟨hA, hB⟩ := howe_on_span hH hp s0 h0 hv
    refine ⟨fun cT hT => ?_, fun cS hS => ?_⟩
    · have hw : (cT.sum fun b z => z • ω (1, b) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun b => ω (1, b)) (fun b => scal (1, b)) cT
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cS, hcS⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hB _ hw (hT s0 hv))
      exact ⟨cS, comb_transfer (LocVac ρ) ρ (fun b => ω (1, b)) (fun a => ω (a, 1)) model
        (fun b => scal (1, b)) (fun a => scal (a, 1)) cT cS s0 h0 hv hcS.symm⟩
    · have hw : (cS.sum fun a z => z • ω (a, 1) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun a => ω (a, 1)) (fun a => scal (a, 1)) cS
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cT, hcT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hA _ hw (hS s0 hv))
      exact ⟨cT, comb_transfer (LocVac ρ) ρ (fun a => ω (a, 1)) (fun b => ω (1, b)) model
        (fun a => scal (a, 1)) (fun b => scal (1, b)) cS cT s0 h0 hv hcT.symm⟩
  · have hz' : ∀ s, LocVac ρ s → s = 0 := by
      intro s hs
      by_contra hne
      exact hz ⟨s, hne, hs⟩
    refine ⟨fun cT _ => ⟨0, fun s hs => ?_⟩, fun cS _ => ⟨0, fun s hs => ?_⟩⟩
    · simp [hz' s hs, Finsupp.sum]
    · simp [hz' s hs, Finsupp.sum]

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeUnramified_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  first | exact @GlobalTheory.Hk3.howe_all_vacua | exact GlobalTheory.Hk3.howe_all_vacua | (intros; apply GlobalTheory.Hk3.howe_all_vacua <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VolqExistsPow
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col GlobalTheory.TopStep

theorem volq_index {G : Type} [Group G] (H : Subgroup G) {q k : ℕ} (hq : q.Prime) (h : ∀ g : G, g ^ q ^ k ∈ H) :
    H.index = 0 ∨ ∃ e : ℕ, H.index = q ^ e := by
  by_cases h0 : H.index = 0
  · exact Or.inl h0
  right
  haveI : H.FiniteIndex := ⟨h0⟩
  haveI := Fact.mk hq
  have hp : IsPGroup q (G ⧸ H.normalCore) := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    intro b
    have := h (b * g * b⁻¹)
    rwa [conj_pow] at this
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hp
  have hd : H.index ∣ q ^ e := by
    rw [← he]
    exact Subgroup.index_dvd_of_le H.normalCore_le
  obtain ⟨e', -, he'⟩ := (Nat.dvd_prime_pow hq).1 hd
  exact ⟨e', he'⟩

theorem volq_choose {q : ℕ} (hq : q.Prime) (a c i : ℕ) (h0 : i ≠ 0) (hi : i ≤ c) : q ^ a ∣ (q ^ (a + c)).choose i := by
  by_cases h : i ≤ q ^ (a + c)
  · have h1 := Nat.factorization_choose_prime_pow_add_factorization hq h h0
    have h2 := Nat.factorization_lt q h0
    rw [hq.pow_dvd_iff_le_factorization (Nat.choose_pos h).ne']
    omega
  · rw [Nat.choose_eq_zero_of_lt (not_le.1 h)]
    exact dvd_zero _

theorem volq_pow_mem {V : Type} [AddCommGroup V] (A B : AddSubgroup V) {q : ℕ} (hq : q.Prime) (b c : ℕ)
    (hAB : ∀ v ∈ A, q ^ b • v ∈ B) (hBA : ∀ v ∈ B, q ^ b • v ∈ A) (r : Module.End ℤ V) (hr : ∀ v ∈ B, r v ∈ B)
    (hn : (r - 1) ^ (c + 1) = 0) : ∀ v ∈ A, (r ^ q ^ (2 * b + c)) v ∈ A := by
  intro v hv
  have hν : ∀ i : ℕ, ∀ v ∈ B, ((r - 1) ^ i) v ∈ B := by
    intro i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (B.sub_mem (hr v hv) hv)
  have e : r = (r - 1) + 1 := by simp
  rw [e, (Commute.one_right _).add_pow, LinearMap.sum_apply]
  refine A.sum_mem fun i _ => ?_
  rw [one_pow, mul_one, ← nsmul_eq_mul', LinearMap.smul_apply]
  rcases eq_or_ne i 0 with rfl | h0
  · simpa using hv
  by_cases hi : i ≤ c
  · obtain ⟨t, ht⟩ := volq_choose hq (2 * b) c i h0 hi
    have h1 := hBA _ (hν i _ (hAB v hv))
    rw [map_nsmul, smul_smul, ← pow_add, ← two_mul] at h1
    rw [ht, mul_comm, mul_smul]
    exact A.nsmul_mem h1 t
  · rw [pow_eq_zero_of_le (by omega) hn]
    simpa using A.zero_mem

section Nil

variable {k : Type} [CommRing k] {n c : ℕ}

theorem volq_lower {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) (i : ℕ) :
    ∀ v ∈ Loc.Ufl k n c (i + 1), r v - v ∈ Loc.Ufl k n c i := by
  intro v hv
  have h1 : v - Loc.atN v (n + i) • Loc.eN k (n + c) (n + i) ∈ Loc.Ufl k n c i := by
    intro l hl
    by_cases h : l.1 = n + i
    · have h2 : n + i < n + c := h ▸ l.2
      have h3 : l = ⟨n + i, h2⟩ := Fin.ext h
      subst h3
      simp [Loc.atN, Loc.eN, h2]
    · have := hv l (by simp only [Set.mem_setOf_eq] at hl ⊢; omega)
      simp [Loc.eN, h, this]
  have h2 := hr.1.1.1 i _ h1
  have h3 := (Loc.Ufl k n c i).smul_mem (Loc.atN v (n + i)) (hr.1.1.2.2 i)
  have h4 := add_mem (sub_mem h2 h1) h3
  convert h4 using 1
  simp only [map_sub, map_smul, smul_sub]
  abel

theorem volq_zero {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) :
    ∀ v ∈ Loc.Ufl k n c 0, r v - v = 0 := by
  intro v hv
  have e : v = Loc.inX k n c fun l => v (Fin.castAdd c l) := by
    funext l
    by_cases h : l.1 < n
    · simp [Loc.inX, h]
    · simp only [Loc.inX, LinearMap.pi_apply, h, dif_neg, not_false_eq_true, LinearMap.zero_apply]
      exact hv l (by simpa using h)
  rw [sub_eq_zero, e]
  exact hr.2 _

theorem volq_nil {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) :
    ((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Fin (n + c) → k)) - 1) ^ (c + 1) = 0 := by
  have h : ∀ i, ∀ v ∈ Loc.Ufl k n c i,
      (((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Fin (n + c) → k)) - 1) ^ (i + 1)) v = 0 := by
    intro i
    induction i with
    | zero => intro v hv; simpa using volq_zero hr v hv
    | succ i ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (volq_lower hr i v hv)
  exact LinearMap.ext fun v => h c v fun l hl => absurd l.2 hl

end Nil

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem volq_exists_pow (a : E) : ∃ b : ℕ, IntAt P ((qOf P : E) ^ b * a) := by
  have hq : P.valuation E (qOf P : E) < 1 := by
    have := (P.valuation_lt_one_iff_mem (K := E) _).2 (qOf_mem (P := P))
    change P.valuation E (algebraMap (𝓞 E) E _) < 1 at this
    rwa [map_natCast] at this
  have : ∃ b : ℕ, P.valuation E ((qOf P : E) ^ b * a) ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, by simp⟩
    have h0 : P.valuation E a ≠ 0 := (map_ne_zero _).2 ha
    obtain ⟨b, hb⟩ := exists_pow_lt₀ hq (Units.mk0 _ h0)⁻¹
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, ← le_mul_inv_iff₀ (zero_lt_iff.2 h0), one_mul]
    simpa using hb.le
  obtain ⟨b, hb⟩ := this
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hb
  exact ⟨b, n, d, d.2, by rw [mul_comm]; exact h⟩

variable [StarRing E]

theorem volq_bound {N : ℕ} (f : Sp E N →ₗ[E] Sp E N) :
    ∃ b : ℕ, ∀ b', b ≤ b' → ∀ v ∈ stdAt E N P, qOf P ^ b' • f v ∈ stdAt E N P := by
  choose g hg using fun p : Fin N × Fin N => volq_exists_pow (P := P) (f (Pi.single p.2 1) p.1)
  refine ⟨Finset.univ.sup g, fun b' hb v hv => mem_stdAt.2 fun i => ?_⟩
  rw [Pi.smul_apply, apply_eq_sum, nsmul_eq_mul, Finset.mul_sum]
  refine intAt_sum _ fun j _ => ?_
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ((Finset.le_sup (f := g) (Finset.mem_univ (i, j))).trans hb)
  have := ((mem_stdAt.1 hv j).mul (hg (i, j))).mul (intAt_pow (intAt_nat (qOf P)) t)
  convert this using 1
  push_cast
  ring

theorem volq_lamY {n c : ℕ} : LocE.lamY P (qOf P) n c 0 = stdAt E (n + c) P := by
  ext v
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt, mem_stdAt]
  simp [LocE.scE]

theorem volq_relIndex (hq : (qOf P).Prime) {n c : ℕ} (J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)))
    (hJ : J ≤ stabL E _ (stdAt E (n + c) P)) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (Loc.N1 E n c ⊓ stabL E _ (stdAt E (n + c) P)).relIndex (Loc.Cbe J h ⊓ Loc.N1 E n c) = 0 ∨
    ∃ e : ℕ, (Loc.N1 E n c ⊓ stabL E _ (stdAt E (n + c) P)).relIndex (Loc.Cbe J h ⊓ Loc.N1 E n c) = qOf P ^ e := by
  obtain ⟨b₁, h₁⟩ := volq_bound (P := P) h.toLinearMap
  obtain ⟨b₂, h₂⟩ := volq_bound (P := P) h.symm.toLinearMap
  have key : ∀ r ∈ Loc.Cbe J h ⊓ Loc.N1 E n c, ∀ v ∈ stdAt E (n + c) P,
      (r ^ qOf P ^ (2 * (b₁ + b₂) + c)) v ∈ stdAt E (n + c) P := by
    intro r hr v hv
    have hs : h⁻¹ * r * h ∈ stabL E _ (stdAt E (n + c) P) := by
      have := hJ (Subgroup.mem_comap.1 hr.1.2)
      simpa using this
    have := volq_pow_mem (stdAt E (n + c) P).toAddSubgroup
      ((stdAt E (n + c) P).toAddSubgroup.comap h.symm.toLinearMap.toAddMonoidHom) hq (b₁ + b₂) c
      (fun v hv => ?_) (fun v hv => ?_) (r.toLinearMap.restrictScalars ℤ) (fun v hv => ?_) (volq_nil hr.2) v hv
    · have e : ∀ m : ℕ, ((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Sp E (n + c))) ^ m) v = (r ^ m) v := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih]; rfl
      rw [e] at this
      exact this
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h₂ _ (by omega) v hv
    · have := h₁ (b₁ + b₂) (by omega) _ hv
      simpa using this
    · have := (hs (h.symm v)).2 hv
      change h.symm (r (h (h.symm v))) ∈ _ at this
      rw [h.apply_symm_apply] at this
      exact this
  refine volq_index _ hq (k := 2 * (b₁ + b₂) + c) fun g => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  refine ⟨pow_mem g.2.2 _, fun v => ⟨fun hv => ?_, key g.1 g.2 v⟩⟩
  have := key g.1⁻¹ (inv_mem g.2) _ hv
  rw [inv_pow] at this
  change (g.1 ^ _).symm _ ∈ _ at this
  rwa [LinearEquiv.symm_apply_apply] at this

end Loc

theorem volumeAtQ : VolumeAtQ := by
  intro X Pr R sharp j P h w hP hd hw
  unfold Loc.volN Jat lamYat
  simp only [if_neg hP]
  rw [volq_lamY, inv_div, map_div₀]
  have hn : ∀ m : ℕ, w.valuation X.K (m : X.K) ≤ 1 := fun m => by
    have := w.valuation_le_one (K := X.K) (m : 𝓞 X.K)
    change w.valuation X.K (algebraMap (𝓞 X.K) X.K _) ≤ 1 at this
    rwa [map_natCast] at this
  have hq : w.valuation X.K (qOf P : X.K) = 1 := by
    have := (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rwa [map_natCast] at this
  rcases volq_relIndex hd.1 (LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j)) inf_le_left h with h0 | ⟨e, he⟩
  · rw [h0]
    simp
  · rw [he, Nat.cast_pow, map_pow, hq, one_pow, div_one]
    exact hn _

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceSkewHermitianGramIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceSkewHermitianGramIntegral
open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem trace_skewHermitian_gram_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam0 σ ϖ e →
  δ * Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ δ hv hδ n n' r JT a y M e Γ hJT hya haM hΓ
  have hmem : ∀ x : L, x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := fun _ => Iff.rfl
  set N := y * M with hNdef
  have hNe : N = (y * (a : Matrix (Fin n) (Fin n) L)) * (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) := by
    rw [hNdef, Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L)]
    have : (a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.one_mul]
  have hN : ∀ q k, N q k * ϖ ^ e k ∈ Formalism.UG.intL L := by
    intro q k
    rw [hNe, Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mul_assoc]
    exact Subring.mul_mem _ (hya q i) (haM i k)
  have hNσ : ∀ p j, σ (N p j) * ϖ ^ e j ∈ Formalism.UG.intL L := by
    intro p j
    have h := hN p j
    rw [hmem] at h ⊢
    rw [map_mul, hv]; rw [map_mul] at h; exact h
  have hG : ∀ j k, (Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k * ϖ ^ (e j + e k) ∈ Formalism.UG.intL L := by
    intro j k
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun q _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    refine Subring.sum_mem _ fun p _ => ?_
    have hc : Formalism.UG.cT σ N j p = σ (N p j) := rfl
    rw [hc, pow_add]
    have : σ (N p j) * (JT : Matrix (Fin n') (Fin n') L) p q * N q k * (ϖ ^ e j * ϖ ^ e k) =
        (σ (N p j) * ϖ ^ e j) * (JT : Matrix (Fin n') (Fin n') L) p q * (N q k * ϖ ^ e k) := by ring
    rw [this]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hNσ p j) (hJT p q)) (hN q k)
  refine Subring.mul_mem _ hδ ?_
  rw [Matrix.trace]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [hmem, map_mul]
  have h1 := hΓ.2 k j
  have h2 := hG j k
  rw [hmem, map_mul, map_pow] at h2
  calc Valued.v (Γ k j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k)
      ≤ Valued.v ϖ ^ (e k + e j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) :=
        mul_le_mul_of_nonneg_right h1 zero_le'
    _ = Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) * Valued.v ϖ ^ (e j + e k) := by
        rw [mul_comm, add_comm]
    _ ≤ 1 := h2

end GlobalTheory.Hk3.GramSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceSkewHermitianGramIntegralStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_skewHermitian_gram_integral_alt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam0 σ ϖ e →
  δ * Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.GramSep.trace_skewHermitian_gram_integral | exact GlobalTheory.Hk3.GramSep.trace_skewHermitian_gram_integral | (intros; apply GlobalTheory.Hk3.GramSep.trace_skewHermitian_gram_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPow
open Matrix

noncomputable section

namespace GlobalTheory.UnramReps

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem le_ofAdd_neg_one_of_lt_one' {y : WithZero (Multiplicative ℤ)} (h : y < 1) :
    y ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem exists_residue_reps' {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2) :
    ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ x ∈ Formalism.UG.intL L, ∃ r ∈ R,
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) (x - r) < 1 := by
  classical
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have hfin : Finite (v.integer ⧸ IsLocalRing.maximalIdeal v.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Finite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring) := hfin
  haveI := Fintype.ofFinite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring)
  let f : v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring → L :=
    fun c => ((Ideal.Quotient.mk_surjective c).choose : L)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    show _ ∈ v.integer
    rw [Valuation.mem_integer_iff]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (Ideal.Quotient.mk_surjective c).choose.2
  · intro x hx
    have hx' : x ∈ v.valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 ((Valuation.mem_integer_iff _ _).1 hx)
    let xs : v.valuationSubring := ⟨x, hx'⟩
    let c := Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring) xs
    refine ⟨f c, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
    have hspec := (Ideal.Quotient.mk_surjective c).choose_spec
    have hmem : xs - (Ideal.Quotient.mk_surjective c).choose ∈
        IsLocalRing.maximalIdeal v.valuationSubring :=
      Ideal.Quotient.eq.1 (hspec.symm)
    rw [Valuation.mem_maximalIdeal_iff] at hmem
    simpa [xs, f] using hmem

theorem exists_reps_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
      ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  intro L _ _ ϖ σ q hU
  classical
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := hU
  obtain ⟨R, hRO, hR⟩ := exists_residue_reps' (L := L) hq hcard
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
  have h0 : v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  have hϖ1 : v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    norm_num
  have hϖO : ϖ ∈ Formalism.UG.intL L := (Valuation.mem_integer_iff _ _).2 hϖ1
  intro K
  induction K with
  | zero =>
    refine ⟨{0}, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton.1 hr]; exact (Formalism.UG.intL L).zero_mem
    · intro x hx
      refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
      rw [sub_zero, pow_zero]
      exact (Valuation.mem_integer_iff _ _).1 hx
  | succ N ih =>
    obtain ⟨T, hTO, hT⟩ := ih
    refine ⟨Finset.image₂ (fun r t => r + ϖ * t) R T, ?_, ?_⟩
    · intro z hz
      obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_image₂.1 hz
      exact (Formalism.UG.intL L).add_mem (hRO r hr) ((Formalism.UG.intL L).mul_mem hϖO (hTO t ht))
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := hR x hx
      have hle : v (x - r) ≤ v ϖ := hϖ ▸ le_ofAdd_neg_one_of_lt_one' hxr
      set y := (x - r) * ϖ⁻¹ with hy
      have hϖ0 : ϖ ≠ 0 := fun h => h0 (by rw [h, map_zero])
      have hyO : y ∈ Formalism.UG.intL L := by
        apply (Valuation.mem_integer_iff _ _).2
        rw [hy, map_mul, map_inv₀]
        calc v (x - r) * (v ϖ)⁻¹ ≤ v ϖ * (v ϖ)⁻¹ := mul_le_mul' hle le_rfl
          _ = 1 := mul_inv_cancel₀ h0
      obtain ⟨t, ht, hyt⟩ := hT y hyO
      refine ⟨r + ϖ * t, Finset.mem_image₂.2 ⟨r, hr, t, ht, rfl⟩, ?_⟩
      have he : x - (r + ϖ * t) = ϖ * (y - t) := by
        rw [hy]; field_simp; ring
      show v (x - (r + ϖ * t)) ≤ v ϖ ^ (N + 1)
      rw [he, map_mul, pow_succ']
      exact mul_le_mul' le_rfl hyt

end GlobalTheory.UnramReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPowStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representatives_mod_uniformizerPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
  Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
    ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  first | exact @GlobalTheory.UnramReps.exists_reps_mod_pow | exact GlobalTheory.UnramReps.exists_reps_mod_pow | (intros; apply GlobalTheory.UnramReps.exists_reps_mod_pow <;> assumption)
end
end

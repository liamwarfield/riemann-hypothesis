module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.KStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.DedekindSR

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.BaseChangeBijective
noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB.StabilizationIso

theorem stab_self (R : Type) [CommRing R] (n : ℕ) (h : n ≤ n) : stab R n n h = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp [stab_apply]

theorem stab_comp (R : Type) [CommRing R] {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (h : n ≤ k) :
    stab R n k h = (stab R m k h₂).comp (stab R n m h₁) := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp only [MonoidHom.comp_apply, stab_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem isIso_stab (R : Type) [CommRing R] [IsDedekindDomain R] (i n : ℕ) (hn : 2 * i + 4 ≤ n) :
    ∀ (m : ℕ) (h : n ≤ m), IsIso (grpHMap (stab R n m h) i) := by
  intro m h
  induction m, h using Nat.le_induction with
  | base =>
    rw [stab_self, grpHComp.1]
    infer_instance
  | succ m hm ih =>
    rw [stab_comp R hm (Nat.le_succ m), grpHComp.2]
    have := PositivityTheory.v8.KStability.kStability R 2 (dedekindSR R) i m (by omega)
    infer_instance

theorem baseChange_bijective {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) [IsIso f] :
    Function.Bijective (LinearMap.baseChange ℝ f.hom) := by
  have h1 : (inv f).hom ∘ₗ f.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, IsIso.hom_inv_id, ModuleCat.hom_id]
  have h2 : f.hom ∘ₗ (inv f).hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id]
  have l1 : (LinearMap.baseChange ℝ (inv f).hom) ∘ₗ LinearMap.baseChange ℝ f.hom = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h1, LinearMap.baseChange_id]
  have l2 : (LinearMap.baseChange ℝ f.hom) ∘ₗ LinearMap.baseChange ℝ (inv f).hom = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h2, LinearMap.baseChange_id]
  refine ⟨Function.LeftInverse.injective (g := LinearMap.baseChange ℝ (inv f).hom) fun x => ?_,
    Function.RightInverse.surjective (g := LinearMap.baseChange ℝ (inv f).hom) fun x => ?_⟩
  · simpa using LinearMap.congr_fun l1 x
  · simpa using LinearMap.congr_fun l2 x

end PositivityTheory.KB.StabilizationIso

end
end

noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sStab_of : SChain → SBridge → SStab := by
  intro hC hB R _ _ k n n' h hn
  obtain ⟨θ, hsurj, hker, hnat⟩ := hB k
  have := StabilizationIso.isIso_stab R (k + 1) n (by omega) n' h
  obtain ⟨hinj, hsur⟩ := StabilizationIso.baseChange_bijective (grpHMap (stab R n n' h) (k + 1))
  have hcyc : ∀ z : Chn (GL (Fin n) R) (k + 1), IsCyc z → IsCyc (cmap (stab R n n' h) (k + 1) z) :=
    fun z hz => by
      unfold IsCyc at hz ⊢
      rw [hC.2.1, hz, map_zero]
  refine ⟨fun z hz hb => ?_, fun z' hz' => ?_⟩
  · have e := hnat _ _ (stab R n n' h) ⟨z, LinearMap.mem_ker.2 hz⟩
      ⟨_, LinearMap.mem_ker.2 (hcyc z hz)⟩ rfl
    rw [(hker _ _).2 hb] at e
    refine (hker _ ⟨z, LinearMap.mem_ker.2 hz⟩).1 (hinj ?_)
    rw [← e, map_zero]
  · obtain ⟨y, hy⟩ := hsur (θ _ ⟨z', LinearMap.mem_ker.2 hz'⟩)
    obtain ⟨w, rfl⟩ := hsurj _ y
    refine ⟨w.1, LinearMap.mem_ker.1 w.2, ?_⟩
    have e := hnat _ _ (stab R n n' h) w ⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ rfl
    exact (hker _ (⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ -
      ⟨z', LinearMap.mem_ker.2 hz'⟩)).1 (by rw [map_sub, e, hy, sub_self])

end PositivityTheory.KB

end

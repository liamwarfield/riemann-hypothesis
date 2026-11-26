module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlattenMany
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelLatticeBaseChange

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SmulMemSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelBundles
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelBundles
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FlattenMany

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (N : I → ℕ) (V : I → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module Ω (V j)] (Γ : ∀ j, (∀ k, ι k) → AddSubgroup (V j)), (∀ j, Module.finrank Ω (V j) = N j ∧ IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset (V j), Γ j c = spanOver (chartRing O (mseg x) c) (S : Set (V j)) ∧ Submodule.span Ω (S : Set (V j)) = ⊤) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j c, mseg (joinCoord x z) c ≠ 0 → LocFree (chartRing O (mseg (joinCoord x z)) c) (N j) (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set (V j))) :=
  @PositivityTheory.Xgn.t_flatten_many

end GlobalTheory.CompanionTheory.Ar.FlattenMany
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelBundlesStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_model_bundles : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (N : I → ℕ) (V : I → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module Ω (V j)] (Γ : ∀ j, (∀ k, ι k) → AddSubgroup (V j)), (∀ j, Module.finrank Ω (V j) = N j ∧ IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset (V j), Γ j c = spanOver (chartRing O (mseg x) c) (S : Set (V j)) ∧ Submodule.span Ω (S : Set (V j)) = ⊤) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j c, mseg (joinCoord x z) c ≠ 0 → LocFree (chartRing O (mseg (joinCoord x z)) c) (N j) (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set (V j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlattenMany.main | exact GlobalTheory.CompanionTheory.Ar.FlattenMany.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FlattenMany.main <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamConstr
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_constr

open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} {x : (Σ k, ι k) → Ω}
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem mono {Γ : (∀ k, ι k) → AddSubgroup V} (h : IsLatFamily o x Γ) {s t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) {v : V} {m m' : ℕ} (hm : m ≤ m') (hv : (mseg x s / mseg x t) ^ m • v ∈ Γ t) :
    (mseg x s / mseg x t) ^ m' • v ∈ Γ t := by
  rw [← Nat.sub_add_cancel hm, pow_add, mul_smul]
  exact h.1 t ht _ (pow_mem (div_mem_chartRing (mseg x) t s) _) _ hv

theorem fam_sub (U : Submodule Ω V) : IsLatFamily o x (fun _ => U.toAddSubgroup) :=
  ⟨fun _ _ a _ _ hv => U.smul_mem a hv, fun _ _ _ _ _ hv => ⟨0, U.smul_mem _ hv⟩⟩

theorem fam_top : IsLatFamily o x (fun _ => (⊤ : AddSubgroup V)) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => ⟨0, trivial⟩⟩

theorem fam_bot : IsLatFamily o x (fun _ => (⊥ : AddSubgroup V)) := fam_sub ⊥

theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊔ B c) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (hA.1 s hs a ha y hy) (hB.1 s hs a ha z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    obtain ⟨m', hm'⟩ := hB.2 s t hs ht z hz
    refine ⟨m + m', ?_⟩
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (mono hA ht (Nat.le_add_right _ _) hm)
      (mono hB ht (Nat.le_add_left _ _) hm')

theorem fam_inf {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊓ B c) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha v hv.1, hB.1 s hs a ha v hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht v hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem fam_map {A : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).map f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨_, hA.1 s hs a ha y hy, hf a y⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    exact ⟨m, _, hm, hf _ y⟩

theorem fam_comap {A : (∀ k, ι k) → AddSubgroup V₁} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).comap f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · rw [AddSubgroup.mem_comap, hf]
    exact hA.1 s hs a ha _ hv
  · obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv
    exact ⟨m, by rw [AddSubgroup.mem_comap, hf]; exact hm⟩

theorem fam_prod {A : (∀ k, ι k) → AddSubgroup V} {B : (∀ k, ι k) → AddSubgroup V₁}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => (A c).prod (B c)) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha _ hv.1, hB.1 s hs a ha _ hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht _ hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem mem_stdLat (R : Subalgebra o Ω) {J : Type} (v : J → Ω) : v ∈ stdLat R J ↔ ∀ j, v j ∈ R :=
  ⟨fun h j => h j trivial, fun h j _ => h j⟩

theorem fam_std (J : Type) [Fintype J] :
    IsLatFamily o x (fun c => stdLat (chartRing o (mseg x) c) J) := by
  refine ⟨fun s _ a ha v hv => ?_, fun s t hs _ v hv => ?_⟩
  · rw [mem_stdLat] at hv ⊢
    exact fun j => mul_mem ha (hv j)
  · rw [mem_stdLat] at hv
    choose m hm using fun j => exists_pow_mul_mem_chartRing (mseg x) s t hs (hv j)
    refine ⟨∑ q, m q, (mem_stdLat _ _).2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hm q)

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

def FG (R : Subalgebra o Ω) (L : AddSubgroup V) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (g : I → V), (∀ i, g i ∈ L) ∧
    ∀ e ∈ L, ∃ a : I → Ω, (∀ i, a i ∈ R) ∧ ∑ i, a i • g i = e

theorem fg_of_locFree {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    FG R L := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  exact ⟨_, inferInstance, fun i => v i, fun i => (v i).2,
    fun e he => ⟨fun i => φ i e, fun i => hφ i e he, hv e⟩⟩

theorem fg_comap {R : Subalgebra o Ω} {L : AddSubgroup V₁} (h : FG R L) (f : V →ₗ[Ω] V₁)
    (hf : Function.Injective f) (hS : Summand L (LinearMap.range f)) :
    FG R (L.comap f.toAddMonoidHom) := by
  obtain ⟨I, hI, g, hg, hL⟩ := h
  obtain ⟨ρ, h1, h2, h3⟩ := hS
  choose y hy using fun i => h1 (g i)
  refine ⟨I, hI, y, fun i => ?_, fun e he => ?_⟩
  · change f (y i) ∈ L
    rw [hy]
    exact h3 _ (hg i)
  · obtain ⟨a, ha, hs⟩ := hL (f e) he
    refine ⟨a, ha, hf ?_⟩
    rw [← h2 (f e) ⟨e, rfl⟩, ← hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hy]

theorem fam_dual {m : ℕ} {A : (∀ k, ι k) → AddSubgroup (Fin m → Ω)} (hA : IsLatFamily o x A)
    (hfg : ∀ c, mseg x c ≠ 0 → FG (chartRing o (mseg x) c) (A c)) :
    IsLatFamily o x (fun c => dotDual (chartRing o (mseg x) c) (A c)) := by
  refine ⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩
  · rw [mem_dotDual] at hw ⊢
    intro v hv
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (hw v hv)
  · rw [mem_dotDual] at hw
    obtain ⟨I, hI, g, hg, hL⟩ := hfg t ht
    have key : ∀ i, ∃ k : ℕ, (mseg x s / mseg x t) ^ k * (g i ⬝ᵥ w) ∈ chartRing o (mseg x) t := by
      intro i
      obtain ⟨k, hk⟩ := hA.2 t s ht hs _ (hg i)
      obtain ⟨k', hk'⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs (hw _ hk)
      refine ⟨k', ?_⟩
      have hu : (mseg x s / mseg x t) ^ k * (mseg x t / mseg x s) ^ k = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (mseg x s), div_self (mul_ne_zero ht hs), one_pow]
      rw [smul_dotProduct, smul_eq_mul] at hk'
      have : (mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w) = (mseg x s / mseg x t) ^ k *
          ((mseg x s / mseg x t) ^ k' * ((mseg x t / mseg x s) ^ k * (g i ⬝ᵥ w))) := by
        linear_combination (-(mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w)) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) hk'
    choose k hk using key
    refine ⟨∑ q, k q, (mem_dotDual _ _ _).2 fun v hv => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hL v hv
    rw [sum_dotProduct]
    refine sum_mem fun q _ => ?_
    have hle : k q ≤ ∑ q, k q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add,
      mul_assoc]
    exact mul_mem (ha q) (mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hk q))

theorem linMap_inj {F : Type} [Zero F] [One F] (n : ℕ) (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) :
    Function.Injective (linMap n χ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro l hl
  funext j
  have := congrFun hl (Pi.single j 1)
  rw [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Finset.sum_eq_single j] at this
  · simpa [h1] using this
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi, h0]
  · simp

end PositivityTheory.Xgn.A_fam_constr

open PositivityTheory.Xgn.A_fam_constr in
theorem PositivityTheory.Xgn.t_fam_constr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D hD
  have hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) :=
    fam_sup hD.famM (fam_map (fam_std _) _ fun a v => smul_comm _ _ _)
  refine ⟨hl1, fun τ => ?_⟩
  obtain ⟨hlie, -, -, -, -, hDel, hTh⟩ := hD.fam τ
  have haf : IsLatFamily O x
      (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) :=
    fam_comap hl1 _ fun a v => (linMap n (fun a => algebraMap O Ω (χ τ a))).map_smul a v
  refine ⟨haf, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hG => ?_⟩
  · exact fam_comap (fam_sup hD.famM (fam_sub _)) _
      fun a v => (LinearMap.toSpanSingleton Ω _ _).map_smul a v
  · exact fam_comap (fam_sup hTh (fam_prod (fam_sub _) fam_bot)) _
      fun a v => Prod.ext ((LinearMap.toSpanSingleton Ω _ _).map_smul a v.1) rfl
  · exact fam_map (fam_inf hTh (fam_prod (fam_sub _) fam_top)) _ fun a v => rfl
  · exact fam_dual hlie fun c hc => fg_of_locFree ((hD.base c hc).free τ).1
  · have hh : IsLatFamily O x
        (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) := by
      refine fam_dual haf fun c hc => fg_comap (fg_of_locFree (hG c hc).l1) _
        (linMap_inj n _ ?_ ?_) ((hG c hc).lin τ)
      · simp [(hD.char.2.2.2.2 τ).1]
      · simp [(hD.char.2.2.2.2 τ).2]
    exact ⟨hh, fam_map (fam_inf hDel (fam_prod hh fam_top)) _ fun a v => rfl⟩
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ImageLatticeBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.ImageLatticeBaseChange

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem isBaseChange_bcMap (C : Type) [Field C] [Algebra Ω C] (m : ℕ) :
    IsBaseChange C (bcMap Ω C (Fin m)) :=
  IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap Ω C)

theorem locFree_div (R : Subalgebra o Ω) {m : ℕ} {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup (Fin m → Ω)) (hL : ∀ v, v ∈ L ↔ ∀ i, w * v i ∈ R) : LocFree R m L := by
  have hb : ∀ a : Fin m → Ω, (∑ q, a q • w⁻¹ • (Pi.single q 1 : Fin m → Ω)) = fun i => a i * w⁻¹ := by
    intro a
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp,
    fun _ => ⟨fun q => w⁻¹ • (Pi.single q 1 : Fin m → Ω), ?_, ?_, ?_⟩⟩
  · intro a ha e he
    rw [hL] at he ⊢
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    exact R.mul_mem ha (he i)
  · have h := (Pi.basisFun Ω (Fin m)).linearIndependent.map'
      (LinearEquiv.smulOfNeZero Ω (Fin m → Ω) w⁻¹ (inv_ne_zero hw)).toLinearMap
      (LinearEquiv.ker _)
    simpa [Function.comp_def] using h
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x = ∑ q, (w * x q) • (w⁻¹ • (Pi.single q 1 : Fin m → Ω)) := by
      rw [hb (fun q => w * x q)]
      funext i
      field_simp
    rw [hx]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · intro e
    constructor
    · rintro ⟨k, hk⟩
      simp only [one_pow, one_smul] at hk
      refine ⟨fun q => w * e q, fun q => ⟨0, by simpa using (hL e).1 hk q⟩, ?_⟩
      rw [hb]
      funext i
      field_simp
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      simp only [pow_zero, one_smul]
      rw [hb, hL]
      intro i
      obtain ⟨k, hk⟩ := ha i
      simp only [one_pow, one_mul] at hk
      field_simp
      exact hk

end PositivityTheory.Xgn.ImageLatticeBaseChange

private theorem dotDual_spanOver_bcMap_eq {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {m k : ℕ} (A : AddSubgroup (Fin m → Ω)) (a γ : Fin k → Fin m → Ω) (ha : ∀ i, a i ∈ A)
    (hγ : ∀ i, γ i ∈ dotDual R A) (hid : ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0) :
    dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' A)) = spanOver RC (bcMap Ω C (Fin m) '' dotDual R A) := by
  have hb : ∀ (v : Fin m → Ω) j, bcMap Ω C (Fin m) v j = algebraMap Ω C (v j) := fun _ _ => rfl
  have hdot : ∀ u v : Fin m → Ω,
      bcMap Ω C (Fin m) u ⬝ᵥ bcMap Ω C (Fin m) v = algebraMap Ω C (u ⬝ᵥ v) := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, hb, map_sum, map_mul]
  apply le_antisymm
  · intro y hy
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hy
    have hy' : y = ∑ i, (bcMap Ω C (Fin m) (a i) ⬝ᵥ y) • bcMap Ω C (Fin m) (γ i) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, hb]
      calc y j = ∑ l, y l * algebraMap Ω C (if l = j then 1 else 0) := by
            simp [apply_ite]
        _ = ∑ i, (∑ l, algebraMap Ω C (a i l) * y l) * algebraMap Ω C (γ i j) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp_rw [← hid, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
            ring
    rw [hy']
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨_, hy _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a i, ha i, rfl⟩, (one_smul _ _).symm⟩),
        _, ⟨γ i, hγ i, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, _, ⟨g, hg, rfl⟩, rfl⟩
    have hg' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R A g).1 hg
    rw [SetLike.mem_coe, PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, rfl⟩ := hv
      rw [smul_dotProduct, dotProduct_smul, hdot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hd (RC.mul_mem hc (hR _ (hg' u hu)))
    | zero => simp
    | add u v _ _ hu hv =>
      rw [add_dotProduct]
      exact add_mem hu hv
    | neg u _ hu =>
      rw [neg_dotProduct]
      exact neg_mem hu

private theorem exists_dual_pair_af_of_summand_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) (hS : Summand (D.l1 R p) (linMap n χ).range)
    (hl1 : LocFree R (Fintype.card F ^ n) (D.l1 R p)) :
    ∃ (k : ℕ) (a γ : Fin k → Fin n → Ω), (∀ i, a i ∈ D.af R p χ) ∧ (∀ i, γ i ∈ dotDual R (D.af R p χ)) ∧
      ∀ l j, ∑ i, a i l * γ i j = if l = j then 1 else 0 := by
  classical
  obtain ⟨π, hπ, hπL⟩ := PositivityTheory.Xgn.GoodLatticeBaseChange.af_retract R D p χ h0 h1 hS
  let L1 : Submodule R ((Fin n → F) → Ω) :=
    { carrier := D.l1 R p
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c v hv => hl1.1 c c.2 v hv }
  obtain ⟨k, φ, u, hφ, hsum⟩ := GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.exists_dualBasis (L := L1) hl1
  refine ⟨k * Fintype.card F ^ n, fun i => π (u (finProdFinEquiv.symm i)),
    fun i j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1)), ?_, ?_, ?_⟩
  · intro i
    exact hπL _ (u _).2
  · intro i
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual]
    intro v hv
    have hv' : v = ∑ j, v j • (Pi.single j 1 : Fin n → Ω) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    have hval : v ⬝ᵥ (fun j => φ (finProdFinEquiv.symm i) (linMap n χ (Pi.single j 1))) =
        φ (finProdFinEquiv.symm i) (linMap n χ v) := by
      conv_rhs => rw [hv']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
    rw [hval]
    exact hφ _ _ hv
  · intro l j
    have h := congrArg (fun e => π e l) (hsum (linMap n χ (Pi.single j 1)))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at h
    rw [show (if l = j then (1 : Ω) else 0) = (Pi.single j 1 : Fin n → Ω) l by simp [Pi.single_apply], ← h]
    exact (finProdFinEquiv.symm.sum_comp
      (fun x => π (u x) l * φ x (linMap n χ (Pi.single j 1)))).trans
      (Finset.sum_congr rfl fun x _ => mul_comm _ _)

private theorem map_snd_spanOver_prodMap_eq {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
    {X Y Xc Yc : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Xc] [Module C Xc] [AddCommGroup Yc]
    [Module C Yc] (f : X → Xc) (g : Y → Yc) (S : AddSubgroup (X × Y)) :
    AddSubgroup.map (AddMonoidHom.snd Xc Yc) (spanOver RC (Prod.map f g '' S)) =
      spanOver RC (g '' AddSubgroup.map (AddMonoidHom.snd X Y) S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, g x.2, ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • Prod.map f g x, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

open PositivityTheory.Xgn.ImageLatticeBaseChange PositivityTheory.Xgn.A_graph_restrict_bc in
theorem PositivityTheory.Xgn.image_lattice_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG hw C _ _ _ _ RC hR τ
  obtain ⟨hp, hwR, ⟨c, hc, hpc⟩, h01, hχ⟩ := hC
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hp
    rw [hpc, mul_zero]
  obtain ⟨hχ0, hχ1, hχR⟩ := hχ τ
  obtain ⟨k, a, γ, ha, hγ, hid⟩ := exists_dual_pair_af_of_summand_locFree D R p (χ τ) hχ0 hχ1 (hG.lin τ) hG.l1
  have hhh : (D.bc RC).hh RC p (fun x => algebraMap Ω C (χ τ x)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) := by
    unfold LieLatticeData.hh
    rw [PositivityTheory.Xgn.GoodLatticeBaseChange.af_bc R RC D p hR (χ τ) hχ0 hχ1 (hG.lin τ)]
    exact dotDual_spanOver_bcMap_eq R RC hR (D.af R p (χ τ)) a γ ha hγ hid
  have hstab : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ := fun a ha => (hB.stable τ a ha).2.1
  have hfst : ∀ v, v ∈ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) ↔ ∀ i, w * v i ∈ R := by
    intro v
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b, c'⟩, hbc, rfl⟩
      have := ((hB.del τ).1 b).1 ⟨c', hbc⟩
      rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat] at this
      exact this
    · intro hv
      obtain ⟨c', hc'⟩ := ((hB.del τ).1 v).2 ((PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 hv)
      exact ⟨(v, c'), hc', rfl⟩
  have hLF := PositivityTheory.Xgn.ImageLatticeBaseChange.locFree_div R hw0 _ hfst
  have hHle : D.hh R p (χ τ) ≤ AddSubgroup.map (AddMonoidHom.fst _ _) (D.Del τ) := by
    intro v hv
    rw [hfst]
    intro i
    have hv' := (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual R _ v).1 hv
    have hmem : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p (χ τ) :=
      hw τ ⟨Pi.single i 1, (PositivityTheory.Xgn.ImageLatticeBaseChange.mem_stdLat R _).2 (fun j => by
        by_cases h : j = i <;> simp [h, Pi.single_apply, R.one_mem, R.zero_mem]), rfl⟩
    have := hv' _ hmem
    simpa [smul_dotProduct, single_dotProduct] using this
  have hHst : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    unfold LieLatticeData.hh at hv ⊢
    rw [PositivityTheory.Xgn.ImageLatticeBaseChange.mem_dotDual] at hv ⊢
    intro u hu
    rw [dotProduct_smul, smul_eq_mul]
    exact R.mul_mem ha (hv u hu)
  have hg := (PositivityTheory.Xgn.t_graph_restrict_bc R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C n) (PositivityTheory.Xgn.ImageLatticeBaseChange.isBaseChange_bcMap C (s τ))
    (D.Del τ) (D.hh R p (χ τ)) n hstab hLF hHle hHst).1
  unfold LieLatticeData.imH
  rw [hhh]
  change AddSubgroup.map _ (spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' ↑(D.Del τ)) ⊓ _) = _
  rw [hg]
  exact map_snd_spanOver_prodMap_eq RC _ _ _
end

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_good2

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {V W : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup W] [Module Ω W]

theorem smul_mem_span (R : Subalgebra o Ω) (S : Set V) {a : Ω} (ha : a ∈ R) {e : V}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  induction he using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, w, hw, rfl⟩ := hy
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨_, mul_mem ha hb, w, hw, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [smul_add]; exact add_mem hy hw
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem spanOver_eq (R : Subalgebra o Ω) (S : Set V) :
    spanOver R S = (Submodule.span R S).toAddSubgroup := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact (Submodule.span R S).smul_mem ⟨a, ha⟩ (Submodule.subset_span he)
  · intro v hv
    change v ∈ Submodule.span R S at hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact AddSubgroup.subset_closure ⟨1, one_mem _, y, hy, (one_smul _ _).symm⟩
    | zero => exact zero_mem _
    | add y w _ _ hy hw => exact add_mem hy hw
    | smul a y _ hy => exact smul_mem_span R S a.2 hy

theorem map_spanOver (R : Subalgebra o Ω) (S : Set V) (f : V →ₗ[Ω] W) :
    (spanOver R S).map f.toAddMonoidHom = spanOver R (f '' S) := by
  rw [spanOver, spanOver, AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, f.map_smul a e⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, e, he, rfl⟩, f.map_smul a e⟩

theorem bc_self {J : Type} (S : Set (J → Ω)) : bcMap Ω Ω J '' S = S := Set.image_id S

theorem bc_self_prod {J : Type} (S : Set (Ω × (J → Ω))) :
    Prod.map (algebraMap Ω Ω) (bcMap Ω Ω J) '' S = S := Set.image_id S

theorem gens (R : Subalgebra o Ω) (hR : IsNoetherianRing R) {N : ℕ} {L₀ : AddSubgroup V}
    (h₀ : LocFree R N L₀) (f : V →ₗ[Ω] W) (hf : Function.Surjective f) (L : AddSubgroup W)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hle : ∀ v ∈ L, ∃ e ∈ L₀, f e = v) {b : Ω} (hb : b ≠ 0)
    (hge : ∀ e ∈ L₀, b • f e ∈ L) :
    ∃ S : Finset W, L = spanOver R (S : Set W) ∧ Submodule.span Ω (S : Set W) = ⊤ := by
  classical
  let L₀' : Submodule R V := { L₀ with smul_mem' := fun a e he => h₀.1 a a.2 e he }
  let L' : Submodule R W := { L with smul_mem' := fun a e he => hst a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L₀') (r := N) h₀
  have hfg : (Submodule.span R (Set.range fun i => f (v i))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hL : L' ≤ Submodule.span R (Set.range fun i => f (v i)) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := hle y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv e, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ (⟨φ i e, hφ i e he⟩ : R) (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨S, hS⟩ : L'.FG := hfg.of_le hL
  refine ⟨S, ?_, ?_⟩
  · rw [spanOver_eq, hS]
  · rw [eq_top_iff]
    intro y _
    obtain ⟨e, rfl⟩ := hf y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv e, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have h1 : b • f (v i) ∈ L' := hge _ (v i).2
    rw [← hS] at h1
    have h2 := Submodule.smul_mem _ b⁻¹ (Submodule.span_le_restrictScalars R Ω _ h1 :
      b • f (v i) ∈ Submodule.span Ω (S : Set W))
    rwa [inv_smul_smul₀ hb] at h2

theorem annSub_min (n i : ℕ) : annSub Ω n (min i n) = annSub Ω n i := by
  unfold annSub
  congr 1
  ext j
  have := j.2
  simp only [Set.mem_setOf_eq]
  omega

theorem vanSub_min (F : Type) [Zero F] (n i : ℕ) : vanSub Ω F n (min i n) = vanSub Ω F n i := by
  unfold vanSub
  congr 1
  ext x
  refine forall_congr' fun j => ?_
  have := j.2
  have : min i n ≤ (j : ℕ) ↔ i ≤ (j : ℕ) := by omega
  rw [this]

theorem kk_min {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (τ : Sg)
    (i : ℕ) : D.kk τ (min i n) = D.kk τ i := by
  rw [LieLatticeData.kk, LieLatticeData.kk, vanSub_min]

theorem injective {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap, mcIdeal, RingHom.mem_ker]
    change GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (algebraMap O _ a) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h.2.2.1] at h1
  exact h1

theorem charData {O : Type} [CommRing O] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) {F : Type} [Zero F] [One F] {Sg : Type} (p : ℕ)
    (hp : p.Prime) (w : O) (χ : Sg → F → O)
    (h : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O) ∧ (0 : F) ≠ 1 ∧
      ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1) (R : Subalgebra O Ω) :
    CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
  obtain ⟨h0, ⟨u, hu, hw⟩, -, h01, hχ⟩ := h
  obtain ⟨u, rfl⟩ := hu
  refine ⟨?_, R.algebraMap_mem _, ⟨algebraMap O Ω ((u⁻¹ : Oˣ) * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩, h01,
    fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
  · rw [← map_natCast (algebraMap O Ω)]
    exact (map_ne_zero_iff _ hinj).2 h0
  · have h2 : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    rw [← map_mul, mul_assoc, ← pow_succ, ← h2, hw, Units.inv_mul_cancel_left, map_natCast]
  · simp only [(hχ τ).1, map_zero]
  · simp only [(hχ τ).2, map_one]

section Point

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
  (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (hR : IsNoetherianRing R) (p : ℕ) (w : Ω)
  (χ : Sg → F → Ω) (hχ : CharData R p w χ) (hB : D.Base R p w)

include hR hχ hB

theorem gens_dual (τ : Sg) (L : AddSubgroup (Fin (r τ) → Ω)) (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L)
    (hle : ∀ m ∈ L, ∃ g, (g, m) ∈ D.Th τ) (hge : ∀ m, (0, m) ∈ D.Th τ → m ∈ L) :
    ∃ S : Finset (Fin (r τ) → Ω), L = spanOver R (S : Set (Fin (r τ) → Ω)) ∧ Submodule.span Ω (S : Set (Fin (r τ) → Ω)) = ⊤ :=
  gens R hR (PositivityTheory.Xgn.t_dotdual_bc R R (fun _ h => h) _ _ (hB.free τ).1).1 LinearMap.id
    Function.surjective_id L hst (fun m hm => ⟨m, ((hB.th τ).2.1 m).1 (hle m hm), rfl⟩) hχ.1
    fun e he => hge _ (((hB.th τ).2.2 _).2 ⟨e, he, rfl⟩)

theorem gens_kk (τ : Sg) (i : ℕ) (hst : ∀ a ∈ R, ∀ v ∈ D.kk τ i, a • v ∈ D.kk τ i) :
    ∃ S : Finset (Fin (r τ) → Ω), D.kk τ i = spanOver R (S : Set (Fin (r τ) → Ω)) ∧ Submodule.span Ω (S : Set (Fin (r τ) → Ω)) = ⊤ := by
  refine gens_dual D R hR p w χ hχ hB τ _ hst ?_ fun m hm => ⟨(0, m), ⟨hm, zero_mem _, trivial⟩, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v.1, hv.1⟩

theorem gens_step (τ : Sg) (i : Fin n)
    (hst : ∀ a ∈ R, ∀ v ∈ (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _),
      a • v ∈ (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) :
    ∃ S : Finset (Fin (r τ) → Ω), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) =
      spanOver R (S : Set (Fin (r τ) → Ω)) ∧ Submodule.span Ω (S : Set (Fin (r τ) → Ω)) = ⊤ := by
  refine gens_dual D R hR p w χ hχ hB τ _ hst ?_ fun m hm => ⟨(0, m), ?_, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hy, z, hz, h⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_comap.1 hv)
    have h2 : y.2 + z.2 = v.2 := congrArg Prod.snd h
    have h3 : z.2 = 0 := hz.2
    rw [h3, add_zero] at h2
    refine ⟨y.1, ?_⟩
    change (y.1, v.2) ∈ _
    rw [← h2]
    exact hy
  · refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup_left ?_)
    simpa using hm

theorem gens_im (τ : Sg) (hst : ∀ a ∈ R, ∀ v ∈ D.imH R p τ (χ τ), a • v ∈ D.imH R p τ (χ τ)) :
    ∃ S : Finset (Fin (s τ) → Ω), D.imH R p τ (χ τ) = spanOver R (S : Set (Fin (s τ) → Ω)) ∧
      Submodule.span Ω (S : Set (Fin (s τ) → Ω)) = ⊤ := by
  have hw : w ≠ 0 := by
    obtain ⟨hp, -, ⟨c, -, hc⟩, -⟩ := hχ
    rintro rfl
    exact hp (by simpa using hc)
  refine gens R hR (hB.free τ).2.2.2 (w⁻¹ • LinearMap.id) (fun v => ⟨w • v, inv_smul_smul₀ hw v⟩) _ hst
    ?_ hw fun e he => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨w • v.2, ((hB.del τ).2.1 _).1 ⟨v.1, hv.1⟩, inv_smul_smul₀ hw _⟩
  · exact ⟨(0, e), ⟨((hB.del τ).2.2.1 e).2 he, zero_mem _, trivial⟩, (smul_inv_smul₀ hw e).symm⟩

end Point

end PositivityTheory.Xgn.A_fam_good2

open PositivityTheory.Xgn.A_fam_good2 in
theorem PositivityTheory.Xgn.t_fam_good2 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx hfn F _ _ _ n Sg _ r s p hp w χ φ D hD hG haf
  classical
  have hinj := injective hx
  obtain ⟨hno, -, hch⟩ := PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x
  have hχ := charData hinj p hp w χ hD.char
  have hfam := (PositivityTheory.Xgn.t_fam_constr O Ω K ι x hinj p hp w χ φ D hD).2
  have hfr := fun c hc τ => ((GlobalTheory.T.lattice_good_base_change (D c) _ p _ _ (hχ _) (hD.base c hc) (hG c hc)).1 τ).1
  let I : Type := Sg ⊕ (Sg × Fin (n + 1)) ⊕ (Sg × Fin (n + 1)) ⊕ (Sg × Fin n) ⊕ Sg
  let M : I → ModuleCat.{0} Ω := fun j => match j with
    | .inl _ => ModuleCat.of Ω (Fin n → Ω)
    | .inr (.inl q) => ModuleCat.of Ω ((Fin n → Ω) ⧸ annSub Ω n q.2)
    | .inr (.inr (.inl q)) => ModuleCat.of Ω (Fin (r q.1) → Ω)
    | .inr (.inr (.inr (.inl q))) => ModuleCat.of Ω (Fin (r q.1) → Ω)
    | .inr (.inr (.inr (.inr τ))) => ModuleCat.of Ω (Fin (s τ) → Ω)
  let Γ : ∀ j, (∀ k, ι k) → AddSubgroup (M j) := fun j => match j with
    | .inl τ => fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))
    | .inr (.inl q) => fun c => ((D c).af (chartRing O (mseg x) c) p
        (fun a => algebraMap O Ω (χ q.1 a))).map (annSub Ω n q.2).mkQ.toAddMonoidHom
    | .inr (.inr (.inl q)) => fun c => (D c).kk q.1 q.2
    | .inr (.inr (.inr (.inl q))) => fun c =>
        ((D c).stepGraph q.1 (fun a => algebraMap O Ω (χ q.1 a)) q.2).map (AddMonoidHom.snd _ _)
    | .inr (.inr (.inr (.inr τ))) => fun c =>
        (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a))
  obtain ⟨K', hK, hK', ι', hι', z, hz, hfree⟩ := GlobalTheory.T.lattice_family_model_bundles O Ω K ι x d hx hfn I
    (fun j => Module.finrank Ω (M j)) (fun j => M j) Γ (by
      rintro (τ | q | q | q | τ)
      · exact ⟨rfl, (hfam τ).1, fun c hc => gens _ (hno c) (hfr c hc τ) LinearMap.id Function.surjective_id
          _ (hfr c hc τ).1 (fun v hv => ⟨v, hv, rfl⟩) one_ne_zero fun e he => (one_smul Ω e).symm ▸ he⟩
      · have h := A_fam_constr.fam_map (hfam q.1).1 (annSub Ω n q.2).mkQ.toAddMonoidHom
          fun a v => (annSub Ω n q.2).mkQ.map_smul a v
        exact ⟨rfl, h, fun c hc => gens _ (hno c) (hfr c hc q.1) (annSub Ω n q.2).mkQ
          (Submodule.mkQ_surjective _) _ (h.1 c hc) (fun v hv => hv) one_ne_zero
          fun e he => ⟨e, he, (one_smul Ω _).symm⟩⟩
      · have h := (hfam q.1).2.2.1 q.2
        exact ⟨rfl, h, fun c hc => gens_kk (D c) _ (hno c) p _ _ (hχ _) (hD.base c hc) _ _ (h.1 c hc)⟩
      · have h := A_fam_constr.fam_map ((hfam q.1).2.1 q.2).2 (AddMonoidHom.snd _ _) fun a v => rfl
        exact ⟨rfl, h, fun c hc => gens_step (D c) _ (hno c) p _ _ (hχ _) (hD.base c hc) _ _ (h.1 c hc)⟩
      · have h := ((hfam τ).2.2.2.2 hG).2
        exact ⟨rfl, h, fun c hc => gens_im (D c) _ (hno c) p _ _ (hχ _) (hD.base c hc) _ (h.1 c hc)⟩)
  refine ⟨K', hK, hK', ι', hι', z, hz, fun c hc => ?_⟩
  obtain ⟨hc1, hle⟩ := (hch K' ι' z).2 c hc
  have hB := hD.base _ hc1
  have hG1 := hG _ hc1
  have e1 := fun τ => (((GlobalTheory.T.lattice_good_base_change _ _ p _ _ (hχ _) hB hG1).2 Ω _ hle).2 τ).1
  have e2 := PositivityTheory.Xgn.kernel_lattice_base_change _ _ p _ _ (hχ _) hB hG1 Ω _ hle
  have e3 := PositivityTheory.Xgn.image_lattice_base_change _ _ p _ _ (hχ _) hB hG1 (haf _ hc1) Ω _ hle
  simp only [bc_self, bc_self_prod, Algebra.algebraMap_self_apply] at e1 e2 e3
  unfold pullFamily
  refine ⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_, fun τ => ?_⟩
  · rw [e1, ← annSub_min]
    refine (PositivityTheory.Xgn.summand_iff_locFree_quot _ _ _ (Module.finrank Ω ((Fin n → Ω) ⧸ annSub Ω n (min i n))) _
      (hfree (.inl τ) c hc)).1 ?_
    rw [map_spanOver]
    exact hfree (.inr (.inl (τ, ⟨min i n, by omega⟩))) c hc
  · have h := hfree (.inr (.inr (.inl (τ, ⟨min i n, by omega⟩)))) c hc
    change LocFree _ (Module.finrank Ω (Fin (r τ) → Ω)) _ at h
    rw [Module.finrank_fin_fun] at h
    rw [← kk_min, (e2 τ).1]
    exact h
  · rw [(e2 τ).2]
    have h := hfree (.inr (.inr (.inr (.inl (τ, i))))) c hc
    have e := map_spanOver (chartRing O (mseg (joinCoord x z)) c)
      ((D (restrictChart c)).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i : Set _)
      (LinearMap.snd Ω Ω (Fin (r τ) → Ω))
    change LocFree _ (Module.finrank Ω (Fin (r τ) → Ω)) _ at h
    rw [Module.finrank_fin_fun] at h
    exact e.symm ▸ h
  · have h := hfree (.inr (.inr (.inr (.inr τ)))) c hc
    change LocFree _ (Module.finrank Ω (Fin (s τ) → Ω)) _ at h
    rw [Module.finrank_fin_fun] at h
    rw [e3]
    exact h
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelComparison
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamGood2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  exact @PositivityTheory.Xgn.t_fam_good2

end GlobalTheory.CompanionTheory.Ar.FamGood2
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelComparisonStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_model_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamGood2.main | exact GlobalTheory.CompanionTheory.Ar.FamGood2.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamGood2.main <;> assumption)
end

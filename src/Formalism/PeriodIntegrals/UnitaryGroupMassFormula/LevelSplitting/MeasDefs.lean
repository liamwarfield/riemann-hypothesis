module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOf

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulVecSpanStable
namespace PI.LevelKSplit.W.Loc

open Submodule

variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}



theorem mulVec_span_stable (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ x ∈ G, A.mulVec x ∈ span O G) : ∀ x ∈ span O G, A.mulVec x ∈ span O G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

private theorem sep_lemma' (c v : Fin r → Fin n → B)
    (h : ∀ a b, c b ⬝ᵥ v a = if a = b then 1 else 0) (g : Fin n → B)
    (hg : g ∈ span B (Set.range v)) : g = ∑ a, (c a ⬝ᵥ g) • v a := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', rfl⟩ := hx
    simp [h]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [dotProduct_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul s x _ hx =>
    simp only [dotProduct_smul, smul_eq_mul, mul_smul]
    rw [← Finset.smul_sum, ← hx]

private theorem units_eq_of_res_eq_of_le_iSup (c v : Fin r → Fin n → B) (h : ∀ a b, c b ⬝ᵥ v a = 0) (g : Fin n → B)
    (hg : g ∈ span B (Set.range v)) (b : Fin r) : c b ⬝ᵥ g = 0 := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', rfl⟩ := hx
    exact h _ _
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
  | smul s x _ hx => rw [dotProduct_smul, hx, smul_zero]

theorem sep (e f ce cf : Fin r → Fin n → B)
    (hee : ∀ a b, ce b ⬝ᵥ e a = 0)
    (hef : ∀ a b, ce b ⬝ᵥ f a = if a = b then 1 else 0)
    (hfe : ∀ a b, cf b ⬝ᵥ e a = if a = b then 1 else 0)
    (GX GW GY : Set (Fin n → B))
    (hGX : GX ⊆ span B (Set.range e)) (hGY : GY ⊆ span B (Set.range f))
    (hGW : ∀ w ∈ GW, ∀ b, ce b ⬝ᵥ w = 0 ∧ cf b ⬝ᵥ w = 0)
    (z y : Fin n → B) (hz : ∀ b, ce b ⬝ᵥ z = 0 ∧ cf b ⬝ᵥ z = 0)
    (hy : y ∈ span O (GX ∪ GW ∪ GY)) (hzy : z - y ∈ span B (Set.range e)) :
    z ∈ span O (GX ∪ GW ∪ GY) := by
  rw [Submodule.span_union, Submodule.span_union] at hy
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
  have hxB : x ∈ span B (Set.range e) :=
    Submodule.span_le.mpr hGX (Submodule.span_le_restrictScalars O B GX hx)
  have huB : u ∈ span B (Set.range f) :=
    Submodule.span_le.mpr hGY (Submodule.span_le_restrictScalars O B GY hu)
  have hwW' : ∀ v ∈ span O GW, ∀ b, ce b ⬝ᵥ v = 0 ∧ cf b ⬝ᵥ v = 0 := by
    intro v0 hv0 b
    induction hv0 using Submodule.span_induction with
    | mem v hv => exact hGW v hv b
    | zero => simp
    | add v v' _ _ h1 h2 => simp [dotProduct_add, h1.1, h1.2, h2.1, h2.2]
    | smul o v _ h1 => simp [dotProduct_smul, h1.1, h1.2]
  have hwW := hwW' w hw
  have hceu : ∀ b, ce b ⬝ᵥ u = 0 := by
    intro b
    have h2 : ce b ⬝ᵥ (z - (x + w + u)) = 0 := units_eq_of_res_eq_of_le_iSup ce e hee _ hzy b
    have h3 : ce b ⬝ᵥ x = 0 := units_eq_of_res_eq_of_le_iSup ce e hee _ hxB b
    rw [dotProduct_sub, dotProduct_add, dotProduct_add, (hz b).1, h3, (hwW b).1] at h2
    linear_combination -h2
  have hu0 : u = 0 := by
    rw [sep_lemma' ce f hef u huB]
    simp [hceu]
  have hzy' := sep_lemma' cf e hfe _ hzy
  have hxe := sep_lemma' cf e hfe x hxB
  have hcoef : ∀ a, cf a ⬝ᵥ (z - (x + w + u)) = -(cf a ⬝ᵥ x) := by
    intro a
    rw [hu0, dotProduct_sub, dotProduct_add, dotProduct_add, (hz a).2, (hwW a).2, dotProduct_zero]
    ring
  have hzx : z - (x + w + u) = -x := by
    rw [hzy']
    simp_rw [hcoef, neg_smul, Finset.sum_neg_distrib]
    rw [← hxe]
  rw [hu0, add_zero, sub_eq_iff_eq_add] at hzx
  rw [hzx, neg_add_cancel_left]
  exact Submodule.span_mono (fun v hv => Or.inl (Or.inr hv)) hw

end PI.LevelKSplit.W.Loc
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MeasDefs
noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

def PlacesCountable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Countable (HeightOneSpectrum (𝓞 F))

def ContPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)),
    Continuous (fun g : HA (Af F) σ J =>
      ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))

def LatBorel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)),
    MeasurableSet[borel (Fin n → Fv F v ⊗[F] E)] (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))

end PI.LevelKSplit.W.Meas
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.RatVMemSpan
noncomputable section

namespace PI.LevelKSplit.W.Glob

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def covR (x : Fin n → E) : Fin n → R ⊗[F] E := fun j => inclR R (∑ i, σ (x i) * J i j)

theorem sigR_inclR (a : E) : sigR R σ (inclR R a) = inclR R (σ a) := by
  simp [sigR, inclR]

theorem hR_ratV_left (x : Fin n → E) (y : Fin n → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R x) y = covR R σ J x ⬝ᵥ y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, covR, ratV, JR, Matrix.map_apply, sigR_inclR, dotProduct,
    map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_comm

theorem covR_ratV (x y : Fin n → E) :
    covR R σ J x ⬝ᵥ ratV (F := F) R y = inclR R (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [covR, ratV, hE, Formalism.UG.hform, dotProduct, Finset.sum_mul, map_sum, map_mul]
  exact Finset.sum_comm

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i
  simp [ratV]

theorem ratV_smul (c : E) (x : Fin n → E) :
    ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
  funext i
  simp [ratV, smul_eq_mul, map_mul]

theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

variable {R σ J}

theorem ratV_mem_span {m : ℕ} (Y : Fin m → Fin n → E) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Set.range Y)) :
    ratV (F := F) R x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [ratV_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [ratV_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [ratV_smul]; exact Submodule.smul_mem _ _ hy

theorem lin_fix_span (g : HA R σ J) {m : ℕ} (Y : Fin m → Fin n → E)
    (hY : ∀ a, lin R σ J g (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E)
    (hy : y ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a))) :
    lin R σ J g y = y := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hY a
  | zero => exact map_zero _
  | add w w' _ _ hw hw' => rw [map_add (f := _), hw, hw']
  | smul c w _ hw => rw [map_smul, hw]

theorem spanR_univ {m : ℕ} (Y : Fin m → Fin n → E) :
    spanR (F := F) R Y Set.univ =
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  simp only [spanR, Set.image_univ]

theorem hE_swap (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hinv, hJ.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem H_fix_e {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, F0, Fin.append_left, Fin.snoc_castSucc] using hk (Fin.castAdd r (Fin.castSucc a))

theorem H_fix_f {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, Fin.append_right] using hk (Fin.natAdd (r + 1) a)

theorem H_perp {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (w : Fin n → E)
    (hw : ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) (b : Fin r) :
    covR R σ J (P.e b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 ∧
      covR R σ J (P.f b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
  have key : ∀ u : Fin n → E, lin R σ J k (ratV (F := F) R u) = ratV (F := F) R u →
      hE σ J u w = 0 → covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
    intro u hu h0
    calc covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w)
        = hR R σ J (lin R σ J k (ratV (F := F) R u)) (lin R σ J k (ratV (F := F) R w)) := by
          rw [hu, hR_ratV_left]
      _ = hR R σ J (ratV (F := F) R u) (ratV (F := F) R w) := by rw [hR_lin]
      _ = 0 := by rw [hR_ratV_left, covR_ratV, h0, map_zero]
  exact ⟨key _ (H_fix_e P k hk b) (hw b).1, key _ (H_fix_f P k hk b) (hw b).2⟩

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom

theorem phiV_inclR (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    phiV v (inclR (Af F) a) = inclR (Fv F v) a := by
  simp [phiV, inclR]

theorem phiV_ratV (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) :
    (fun i => phiV v (ratV (F := F) (Af F) x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  exact phiV_inclR v (x i)

theorem phiV_cov (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) (y : Fin n → Af F ⊗[F] E) :
    phiV v (covR (Af F) σ J x ⬝ᵥ y) = covR (Fv F v) σ J x ⬝ᵥ fun i => phiV v (y i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul, covR, phiV_inclR]

theorem phiV_span (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (Y : Fin m → Fin n → E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ spanR (F := F) (Af F) Y Set.univ) :
    (fun i => phiV v (y i)) ∈
      Submodule.span (Fv F v ⊗[F] E) (Set.range fun a => ratV (F := F) (Fv F v) (Y a)) := by
  rw [spanR_univ] at hy
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [phiV_ratV]
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero =>
    have h0 : (fun i => phiV v ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := by
      funext i; simp
    rw [h0]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' =>
    have h1 : (fun i => phiV v ((w + w') i)) = (fun i => phiV v (w i)) + fun i => phiV v (w' i) := by
      funext i; simp
    rw [h1]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
    have h1 : (fun i => phiV v ((c • w) i)) = phiV v c • fun i => phiV v (w i) := by
      funext i; simp
    rw [h1]; exact Submodule.smul_mem _ _ hw

theorem compV_mulVec (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J) (x : Fin n → Af F ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (fun i => phiV v (x i)) =
      fun i => phiV v (lin (Af F) σ J g x i) := by
  funext i
  exact (RingHom.map_mulVec (phiV v)
    (HA.mat (R := Af F) (σ := σ) (J := J) g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) x i).symm

theorem mem_Kf (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ ∀ v, ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ := by
  simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply] <;>
    exact Iff.rfl

end Loc

end PI.LevelKSplit.W.Glob
end
end

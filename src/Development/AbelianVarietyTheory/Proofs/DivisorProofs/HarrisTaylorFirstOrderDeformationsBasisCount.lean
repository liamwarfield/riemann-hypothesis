module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartDeformationDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerSkewDimSemisimpleTwoRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerSkewDimSemisimpleTwoRoots
open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model GlobalTheory.UPel.Sm.KSCount

noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

theorem ksDim_of_eigen_reduce : ∀ (k : Type) (H : Type 1) (O : Type) [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (ρ : O →+* Module.End k H) (st : O → O) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (w : O) (r r' : k) (d : ℕ), Function.Surjective st → (∀ b x y, φ (ρ b x) y = φ x (ρ (st b) y)) → (∀ x y, φ x y = -φ y x) → (∀ x, (∀ y, φ x y = 0) → x = 0) → (∀ x ∈ Fil, ∀ y ∈ Fil, φ x y = 0) → 2 * Module.finrank k Fil = Module.finrank k H → (∀ a, ∀ x ∈ Fil, ρ a x ∈ Fil) → (∀ a, ρ w * ρ a = ρ a * ρ w) → (ρ w - r • 1) * (ρ w - r' • 1) = 0 → r ≠ r' → (∀ x y, φ (ρ w x) y = φ x ((r + r') • y - ρ w y)) → Z ≤ LinearMap.range (ρ w - r' • 1) → KSDim ρ 0 (Fil ⊔ LinearMap.range (ρ w - r • 1)) Z d → KSDim ρ φ Fil Z d := by
  intro k H O _ _ _ _ _ ρ st φ Fil Z w r r' d hst hadj hskew hnd hiso hdim hstab hcomm hA hr hφw hZ hd
  set A := ρ w with hAdef
  have hA2 : ∀ x, A (A x) = (r + r') • A x - (r * r') • x := by
    intro x
    have h := LinearMap.congr_fun hA x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, LinearMap.zero_apply] at h
    linear_combination (norm := module) h
  have hrr : r - r' ≠ 0 := sub_ne_zero.2 hr
  set c := (r - r')⁻¹ with hc
  have hc1 : c * (r - r') = 1 := inv_mul_cancel₀ hrr
  let P : Module.End k H := c • (A - r' • 1)
  have hPx : ∀ x, P x = c • (A x - r' • x) := fun x => by simp [P]
  have hPA : ∀ x, A (P x) = r • P x := by
    intro x; rw [hPx, map_smul, map_sub, map_smul, hA2]
    linear_combination (norm := module) (0:k) • x
  have hPfix : ∀ x, A x = r • x → P x = x := by
    intro x hx; rw [hPx, hx]
    linear_combination (norm := module) hc1 • x
  have hPkill : ∀ x, A x = r' • x → P x = 0 := by
    intro x hx; rw [hPx, hx]; simp
  have hQA : ∀ x, A (x - P x) = r' • (x - P x) := by
    intro x; rw [map_sub, hPA]
    have : A x - r' • x = (r - r') • P x := by rw [hPx, smul_smul, mul_comm, hc1, one_smul]
    linear_combination (norm := module) this
  have hPP : ∀ x, P (P x) = P x := fun x => hPfix _ (hPA x)
  have hPQ : ∀ x, P (x - P x) = 0 := fun x => hPkill _ (hQA x)

  have hAρ : ∀ a x, A (ρ a x) = ρ a (A x) := fun a x => LinearMap.congr_fun (hcomm a) x
  have hPρ : ∀ a x, P (ρ a x) = ρ a (P x) := by
    intro a x; rw [hPx, hPx, hAρ, map_smul, map_sub, map_smul]
  have hPFil : ∀ x ∈ Fil, P x ∈ Fil := fun x hx => by
    rw [hPx]; exact Fil.smul_mem _ (Fil.sub_mem (hstab w x hx) (Fil.smul_mem _ hx))
  have hQFil : ∀ x ∈ Fil, x - P x ∈ Fil := fun x hx => Fil.sub_mem hx (hPFil x hx)
  have hφeig : ∀ (s t : k), s ≠ t → s + t = r + r' → ∀ u v, A u = s • u → A v = s • v → φ u v = 0 := by
    intro s t hst' hsum u v hu hv
    have h := hφw u v
    rw [hu, hv] at h
    simp only [map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, smul_eq_mul] at h
    have h2 : (s - t) * φ u v = 0 := by linear_combination h - (φ u v) * hsum
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hst')
  have hφPP : ∀ x y, φ (P x) (P y) = 0 := fun x y => hφeig r r' hr rfl _ _ (hPA x) (hPA y)
  have hφQQ : ∀ x y, φ (x - P x) (y - P y) = 0 := fun x y =>
    hφeig r' r (Ne.symm hr) (add_comm _ _) _ _ (hQA x) (hQA y)
  have hφdec : ∀ a b, φ a b = φ (P a) (b - P b) + φ (a - P a) (P b) := by
    intro a b
    have e : φ a b = φ (P a + (a - P a)) (P b + (b - P b)) := by simp
    rw [e]
    simp only [map_add (f := _), LinearMap.add_apply, hφPP, hφQQ]
    ring
  have hnd' : φ.Nondegenerate := ⟨hnd, fun y h => hnd y (fun x => by rw [hskew, h x, neg_zero])⟩
  have hperp : ∀ v, (∀ y ∈ Fil, φ v y = 0) → v ∈ Fil := by
    have hle : Fil ≤ φ.orthogonal Fil := by
      intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      exact hiso y hy x hx
    have hdim2 := LinearMap.BilinForm.finrank_orthogonal hnd' Fil
    have heq : Fil = φ.orthogonal Fil := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro v hv
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change φ y v = 0
    rw [hskew, hv y hy, neg_zero]

  have hAP : ∀ v, A v - r' • v = (r - r') • P v := fun v => by
    rw [hPx, smul_smul, mul_comm, hc1, one_smul]
  have hPAc : ∀ x, P (A x) = A (P x) := fun x => by rw [hPx, hPx, map_smul, map_sub, map_smul]
  set G := Fil ⊔ LinearMap.range (A - r • 1) with hG
  have hrangeP : ∀ y ∈ LinearMap.range (A - r • 1), P y = 0 := by
    rintro _ ⟨z, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hPAc, hPA, sub_self]
  have hFilG : Fil ≤ G := le_sup_left
  have hmemG : ∀ x ∈ G, P x ∈ Fil := by
    intro x hx
    obtain ⟨f, hf, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), hrangeP y hy, add_zero]
    exact hPFil f hf
  have hQG : ∀ x, x - P x ∈ G := by
    intro x
    apply Submodule.mem_sup_right
    refine ⟨(-c) • x, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    have h := hAP x
    linear_combination (norm := module) (-c) • h - hc1 • P x + hc1 • x
  have hZP : ∀ z ∈ Z, P z = z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hZ hz
    apply hPfix
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hA2]
    module
  have hwQ : ∀ (F : Submodule k H) v, r • v - A v ∈ F → v - P v ∈ F := by
    intro F v hv
    have e : v - P v = c • (r • v - A v) := by
      have h := hAP v
      linear_combination (norm := module) c • h - hc1 • v + hc1 • P v
    rw [e]; exact F.smul_mem _ hv
  have hwP : ∀ (F : Submodule k H) v, r' • v - A v ∈ F → P v ∈ F := by
    intro F v hv
    have e : P v = (-c) • (r' • v - A v) := by
      have h := hAP v
      linear_combination (norm := module) (-c) • h - hc1 • P v
    rw [e]; exact F.smul_mem _ hv
  have L1 : ∀ v y, φ (P v) y = φ (P v) (y - P y) := fun v y => by
    rw [hφdec (P v) y]; simp [hPP]
  have L2 : ∀ v y, φ (v - P v) y = φ v (P y) := fun v y => by
    rw [hφdec (v - P v) y, hφdec v (P y)]; simp [hPP, hPQ]
  have L3 : ∀ x v, φ x (P v) = φ (x - P x) (P v) := fun x v => by
    rw [hφdec x (P v)]; simp [hPP]
  have L4 : ∀ x v, φ x (v - P v) = φ (P x) v := fun x v => by
    rw [hφdec x (v - P v), hφdec (P x) v]; simp [hPP, hPQ]
  have hQcrit : ∀ v, (∀ y ∈ Fil, φ v (P y) = 0) → v - P v ∈ Fil := by
    intro v hv
    apply hperp
    intro y hy
    rw [L2]; exact hv y hy

  let conj : (H →ₗ[k] H) →ₗ[k] (H →ₗ[k] H) :=
    { toFun := fun g => P ∘ₗ g ∘ₗ P
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  have hconj : ∀ g x, conj g x = P (g (P x)) := fun _ _ => rfl
  have hi : ∀ g, IsKS ρ φ Fil Z g → IsKS ρ 0 G Z (conj g) := by
    intro g hg
    refine ⟨fun a x hx => ?_, fun x hx => ?_, fun x _ y _ => by simp⟩
    · rw [hconj, hconj, hPρ a x, ← hPρ a (g (P x)), ← map_sub]
      exact hFilG (hPFil _ (hg.1 a _ (hmemG x hx)))
    · rw [hconj, hZP x hx]; exact hFilG (hPFil _ (hg.2.1 x hx))
  have hker : ∀ g, IsKS ρ φ Fil Z g → ((∀ x ∈ Fil, g x ∈ Fil) ↔ (∀ x ∈ G, conj g x ∈ G)) := by
    intro g hg
    constructor
    · intro h x hx
      rw [hconj]; exact hFilG (hPFil _ (h _ (hmemG x hx)))
    · intro h
      have hPpart : ∀ u ∈ Fil, P (g (P u)) ∈ Fil := by
        intro u hu
        have := hmemG _ (h (P u) (hFilG (hPFil u hu)))
        rwa [hconj, hPP, hPP] at this
      have hgP : ∀ u ∈ Fil, g (P u) ∈ Fil := by
        intro u hu
        have hq : g (P u) - P (g (P u)) ∈ Fil := by
          apply hwQ
          have := hg.1 w (P u) (hPFil u hu)
          rwa [← hAdef, hPA, map_smul] at this
        have := Fil.add_mem hq (hPpart u hu)
        rwa [sub_add_cancel] at this
      intro x hx
      have hu : x - P x ∈ Fil := hQFil x hx
      have hp : P (g (x - P x)) ∈ Fil := by
        apply hwP
        have := hg.1 w (x - P x) hu
        rwa [← hAdef, hQA, map_smul] at this
      have hq : g (x - P x) - P (g (x - P x)) ∈ Fil := by
        apply hQcrit
        intro y hy
        have h1 := hg.2.2 (x - P x) hu (P y) (hPFil y hy)
        have h2 := hiso (x - P x) hu _ (hgP y hy)
        linear_combination h1 - h2
      have e : g x = g (P x) + (P (g (x - P x)) + (g (x - P x) - P (g (x - P x)))) := by
        rw [add_sub_cancel, ← map_add (f := _), add_sub_cancel]
      rw [e]
      exact Fil.add_mem (hgP x hx) (Fil.add_mem hp hq)

  have hiii : ∀ f', IsKS ρ 0 G Z f' → ∃ g, IsKS ρ φ Fil Z g ∧ ∀ x ∈ G, conj g x - f' x ∈ G := by
    intro f' hf'
    have hinj : Function.Injective φ.flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      apply hnd v
      intro u
      rw [hskew]
      have : φ u v = 0 := LinearMap.congr_fun hv u
      rw [this, neg_zero]
    have hsurj : Function.Surjective φ.flip :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq).symm).1 hinj
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective φ.flip (LinearMap.range_eq_top.2 hsurj)
    let L : H →ₗ[k] H := P ∘ₗ f' ∘ₗ P
    let T : H →ₗ[k] H := s ∘ₗ (-(L.dualMap ∘ₗ φ.flip))
    have hT : ∀ u v, φ u (T v) = -φ (P (f' (P u))) v := by
      intro u v
      have := LinearMap.congr_fun (LinearMap.congr_fun hs (-(L.dualMap ∘ₗ φ.flip) v)) u
      simpa [T, L] using this
    let g : H →ₗ[k] H := L + (1 - P) ∘ₗ T ∘ₗ (1 - P)
    have hg : ∀ x, g x = P (f' (P x)) + (T (x - P x) - P (T (x - P x))) := fun x => by
      simp [g, L]
    have hT0 : T 0 = 0 := map_zero T
    refine ⟨g, ⟨fun a x hx => ?_, fun z hz => ?_, fun x _ y _ => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨q, hq⟩ : ∃ q, q = x - P x := ⟨_, rfl⟩
      obtain ⟨e, he⟩ : ∃ e, e = T (ρ a q) - ρ a (T q) := ⟨_, rfl⟩
      have hqF : q ∈ Fil := hq ▸ hQFil x hx
      have eq : g (ρ a x) - ρ a (g x) = P (f' (ρ a (P x)) - ρ a (f' (P x))) + (e - P e) := by
        have hq' : ρ a x - P (ρ a x) = ρ a q := by rw [hq, hPρ, ← map_sub]
        rw [hg, hg, hq', he, ← hq]
        simp only [hPρ, map_sub, map_add (f := _)]
        abel
      rw [eq]
      refine Fil.add_mem (hmemG _ (hf'.1 a _ (hFilG (hPFil x hx)))) (hQcrit e fun y hy => ?_)
      set u := P y with hu
      set t := T q with ht
      have hm : P (f' (ρ (st a) u)) - ρ (st a) (P (f' u)) ∈ Fil := by
        rw [← hPρ (st a) (f' u), ← map_sub]; exact hmemG _ (hf'.1 (st a) u (hFilG (hPFil y hy)))
      have h4 := hiso _ hm q hqF
      rw [LinearMap.map_sub₂] at h4
      have F2 : φ u (T (ρ a q)) = -φ (P (f' u)) (ρ a q) := by rw [hT, hu, hPP]
      have F5 : φ (ρ (st a) u) t = -φ (P (f' (ρ (st a) u))) q := by rw [ht, hT, hu, hPρ, hPP]
      have F3 := hadj a t u
      have F7 := hadj a q (P (f' u))
      have S1 := hskew (T (ρ a q)) u
      have S2 := hskew t (ρ (st a) u)
      have S3 := hskew (P (f' u)) (ρ a q)
      have S4 := hskew q (ρ (st a) (P (f' u)))
      rw [he, LinearMap.map_sub₂]
      linear_combination S1 - F2 + S3 - F7 - S4 - F3 - S2 + F5 - h4
    · rw [hg, hZP z hz, sub_self, hT0, map_zero, sub_zero, add_zero]
      exact hmemG _ (hf'.2.1 z hz)
    · have ex : φ (g x) y = φ (P (f' (P x))) y + φ (T (x - P x) - P (T (x - P x))) y := by
        rw [hg, map_add (f := _), LinearMap.add_apply]
      have ey : φ x (g y) = φ x (P (f' (P y))) + φ x (T (y - P y) - P (T (y - P y))) := by
        rw [hg, map_add (f := _)]
      have K1 := L1 (f' (P x)) y
      have K2 := L2 (T (x - P x)) y
      have K3 := L3 x (f' (P y))
      have K4 := L4 x (T (y - P y))
      have K5 := hT (P x) (y - P y)
      have K6 := hT (P y) (x - P x)
      rw [hPP] at K5 K6
      have K7 := hskew (T (x - P x)) (P y)
      have K8 := hskew (x - P x) (P (f' (P y)))
      linear_combination ex + ey + K1 + K2 + K3 + K4 + K5 + K7 - K6 + K8
    · rw [hconj, hg, hPP, sub_self, hT0, map_zero, sub_zero, add_zero, hPP]
      have hu : x - P x ∈ G := hQG x
      have hp : P (f' (x - P x)) ∈ G := hwP G _ (by
        have := hf'.1 w (x - P x) hu
        rwa [← hAdef, hQA, map_smul] at this)
      have hq1 := hQG (f' (x - P x))
      have hq2 := hQG (f' (P x))
      have e1 : f' x = f' (P x) + f' (x - P x) := by rw [← map_add (f := _), add_sub_cancel]
      have e : P (f' (P x)) - f' x = -(f' (P x) - P (f' (P x))) -
          (P (f' (x - P x)) + (f' (x - P x) - P (f' (x - P x)))) := by rw [e1]; abel
      rw [e]
      exact G.sub_mem (G.neg_mem hq2) (G.add_mem hp hq1)

  set p := ksSub ρ φ Fil Z with hp
  have hmap : p.map (cls G ∘ₗ conj) = (ksSub ρ 0 G Z).map (cls G) := by
    ext m
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨conj g, hi g hg, rfl⟩
    · rintro ⟨f', hf', rfl⟩
      obtain ⟨g, hg, hgf⟩ := hiii f' hf'
      exact ⟨g, hg, (cls_eq_iff (Fil := G) _ _).2 hgf⟩
  have hkerEq : LinearMap.ker (cls Fil ∘ₗ p.subtype) = LinearMap.ker ((cls G ∘ₗ conj) ∘ₗ p.subtype) := by
    ext ⟨g, hg⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
    have e1 : cls Fil g = 0 ↔ ∀ x ∈ Fil, g x ∈ Fil := by
      rw [← (cls Fil).map_zero, cls_eq_iff]; simp
    have e2 : cls G (conj g) = 0 ↔ ∀ x ∈ G, conj g x ∈ G := by
      rw [← (cls G).map_zero, cls_eq_iff]; simp
    rw [e1, e2]
    exact hker g hg
  have h1 := finrank_map_add_ker p (cls Fil)
  have h2 := finrank_map_add_ker p (cls G ∘ₗ conj)
  rw [hkerEq] at h1
  rw [hmap] at h2
  have hfin : finrank k (p.map (cls Fil)) = finrank k ((ksSub ρ 0 G Z).map (cls G)) := by omega
  have hd' := KSDim.unique hd (ksDim_finrank ρ 0 G Z)
  have := ksDim_finrank ρ φ Fil Z
  rwa [← hp, hfin, ← hd'] at this

end GlobalTheory.UPel.Sm.KSCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerSkewDimSemisimpleTwoRootsStatement
open GlobalTheory.UPel.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots : ∀ (k : Type) (H : Type 1) (O : Type) [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (ρ : O →+* Module.End k H) (st : O → O) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (w : O) (r r' : k) (d : ℕ), Function.Surjective st → (∀ b x y, φ (ρ b x) y = φ x (ρ (st b) y)) → (∀ x y, φ x y = -φ y x) → (∀ x, (∀ y, φ x y = 0) → x = 0) → (∀ x ∈ Fil, ∀ y ∈ Fil, φ x y = 0) → 2 * Module.finrank k Fil = Module.finrank k H → (∀ a, ∀ x ∈ Fil, ρ a x ∈ Fil) → (∀ a, ρ w * ρ a = ρ a * ρ w) → (ρ w - r • 1) * (ρ w - r' • 1) = 0 → r ≠ r' → (∀ x y, φ (ρ w x) y = φ x ((r + r') • y - ρ w y)) → Z ≤ LinearMap.range (ρ w - r' • 1) → KSDim ρ 0 (Fil ⊔ LinearMap.range (ρ w - r • 1)) Z d → KSDim ρ φ Fil Z d := by
  first | exact @GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce | exact GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce | (intros; apply GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {k E : Type*} [Field k] [Ring E] [Algebra k E] (X : E) (tr nm : ℤ) (r r' : k)
    (hX : X * X = (tr : E) * X - (nm : E)) (hs : r + r' = tr) (hp : r * r' = nm) :
    (X - r • (1 : E)) * (X - r' • (1 : E)) = 0 := by
  have htr : (tr : E) = algebraMap k E r + algebraMap k E r' := by rw [← map_add (f := _), hs, map_intCast]
  have hnm : (nm : E) = algebraMap k E r * algebraMap k E r' := by rw [← map_mul, hp, map_intCast]
  rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_one, sub_mul, mul_sub, mul_sub, hX, htr, hnm,
    ← Algebra.commutes r' X]
  noncomm_ring

end GlobalTheory.HTCount

namespace GlobalTheory.HTCount

theorem ksDim_at_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ
  obtain ⟨hfd, hdim, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k t o₀ β ht φ hφ
  have hnd := GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate p D R b N hN hNp k t o₀ β ht φ hφ
  have hadj := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k t o₀ β ht φ hφ
  have hcount := GlobalTheory.T.harrisTaylor_rho_part_deformation_dim p D R b N hN hNp k t o₀ β ht
  haveI := hfd
  have hstab : ∀ a, ∀ x ∈ Fil o₀.A, crysAct o₀ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [crysAct_apply]; exact push_mem_Fil _ hx
  have hcomm : ∀ a, crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) * crysAct o₀ a = crysAct o₀ a * crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hsurj : Function.Surjective (fun c : D.O => (D.star c).unop) := fun a => ⟨(D.star a).unop, D.star_star a⟩

  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hωsq : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hw2 : algebraMap (𝓞 D.F) D.O D.ω * algebraMap (𝓞 D.F) D.O D.ω =
      (D.tr : D.O) * algebraMap (𝓞 D.F) D.O D.ω - (D.nm : D.O) := by
    rw [← map_mul, hωsq, map_sub, map_mul, map_intCast, map_intCast]
  have hstw : (D.star (algebraMap (𝓞 D.F) D.O D.ω)).unop = (D.tr : D.O) - algebraMap (𝓞 D.F) D.O D.ω := by
    rw [D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast]
  have hrr : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this
  have hsum : β b.ρ + ((D.tr : k) - β b.ρ) = (D.tr : k) := by ring
  have hdisc : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) ≠ 0 := by
    have hp : p.Prime := Fact.out
    have hnd : ¬ p ∣ (D.tr ^ 2 - 4 * D.nm).natAbs := fun h => D.disc_p (Int.ofNat_dvd_left.2 h)
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hu := (b.unit _ hcop).map β
    rw [map_natCast] at hu
    intro h0
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast] at h0; exact hu.ne_zero h0
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h0; exact hu.ne_zero h0
  have hne : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    apply hdisc
    push_cast
    linear_combination (2 * β b.ρ - (D.tr : k)) * h + 4 * hrr
  have hZ : lieZ o₀ β ≤ LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨n, lam, c, y, ⟨y₀, rfl⟩, -, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ⟨crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y₀, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    congr 1
    rw [sub_mul, mul_sub, hcomm, smul_mul_assoc, mul_smul_comm, _root_.one_mul, _root_.mul_one]
  generalize lieZ o₀ β = Z at hZ hcount ⊢
  generalize crysAct o₀ = ρ at hstab hcomm hadj hcount hZ ⊢
  generalize algebraMap (𝓞 D.F) D.O D.ω = w at hw2 hstw hcomm hcount hZ
  have hq := sub_smul_mul_sub_smul_eq_zero_of_quadratic (ρ w) D.tr D.nm (β b.ρ) ((D.tr : k) - β b.ρ)
    (by rw [← map_mul, hw2, map_sub, map_mul, map_intCast, map_intCast]) hsum hrr
  have hwadj : ∀ x y, φ (ρ w x) y = φ x ((β b.ρ + ((D.tr : k) - β b.ρ)) • y - ρ w y) := fun x y => by
    rw [hadj, hstw, map_sub, map_intCast, hsum, LinearMap.sub_apply, Module.End.intCast_apply,
      Int.cast_smul_eq_zsmul]
  exact GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots k (HdR o₀.A) D.O ρ (fun c => (D.star c).unop) φ (Fil o₀.A) Z w (β b.ρ) ((D.tr : k) - β b.ρ) _ hsurj
    hadj hskew hnd hiso hdim hstab hcomm hq hne hwadj hZ hcount

end GlobalTheory.HTCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDimStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  first | (exact @GlobalTheory.HTCount.ksDim_at_point) | (exact GlobalTheory.HTCount.ksDim_at_point) | (intros; apply GlobalTheory.HTCount.ksDim_at_point  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderHodgeEqKodairaSpencerGraph
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFil
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount.LieZFil

theorem omega_sq {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) :
    D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
  rw [← D.tr_eq, ← D.nm_eq]; ring

theorem end_sq {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (h : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) (act (algebraMap (𝓞 D.F) D.O D.ω) h) =
      (D.tr : C) • act (algebraMap (𝓞 D.F) D.O D.ω) h - (D.nm : C) • h := by
  have e := congrArg (fun x => act (algebraMap (𝓞 D.F) D.O x) h) (omega_sq D)
  simp only [map_mul, map_sub, map_intCast, Module.End.mul_apply, LinearMap.sub_apply] at e
  rw [e]
  simp [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

theorem rho_part_eig {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (ρ : C) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0) (y : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) -
      ρ • ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, end_sq]
  have hn : (D.nm : C) = ρ * (D.tr - ρ) := by linear_combination hρ
  rw [hn]
  module

theorem sum_mem_fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {C : Type} [CommRing C] [IsLocalRing C] (β : R →+* C)
    {s : Sp C ⟶ Sp R} (hs : s = spMap β) (o : GlobalTheory.UPel.HT.Obj b N s) {r : ℕ} (lam : Fin r → C)
    (c : Fin r → 𝓞 D.F) (hlam : ∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) (y : HdR o.A) :
    ∑ l, lam l • GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O (c l))
      ((GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) -
        ((D.tr : C) - β b.ρ) • 1) y) ∈ Fil o.A := by
  set act := GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act with hact
  set u := (act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - β b.ρ) • 1) y with hu
  have hfil : ∀ (x : D.O) {h : HdR o.A}, h ∈ Fil o.A → act x h ∈ Fil o.A := fun x h hh => by
    haveI := o.act.hom x
    exact push_mem_Fil (o.act.act x) hh
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hω : act (algebraMap (𝓞 D.F) D.O D.ω) u - β b.ρ • u ∈ Fil o.A := by
    rw [hu, rho_part_eig act (β b.ρ) hρ y]; exact zero_mem _
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C β s hs o u hω
  set c' := fun l => algebraMap (𝓞 D.F) D.O (c l)
  have h1 : ∀ l, act (c' l) u - ∑ i, act (c' l) (w i) ∈ Fil o.A := fun l => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sub]; exact hfil _ hsum
  have h2 : ∀ i, ∑ l, lam l • act (c' l) (w i) ∈ Fil o.A := fun i => by
    have e : ∑ l, lam l • act (c' l) (w i) = ∑ l, lam l • (act (c' l) (w i) - β (b.t i (c l)) • w i) +
        (∑ l, lam l * β (b.t i (c l))) • w i := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, mul_smul]; abel
    rw [e, hlam i, zero_smul, add_zero]
    exact sum_mem fun l _ => Submodule.smul_mem _ _ (hw i (c l))
  have e : ∑ l, lam l • act (c' l) u = ∑ l, lam l • (act (c' l) u - ∑ i, act (c' l) (w i)) +
      ∑ i, ∑ l, lam l • act (c' l) (w i) := by
    rw [Finset.sum_comm (f := fun i l => lam l • act (c' l) (w i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.smul_sum, ← smul_add, sub_add_cancel]
  show ∑ l, lam l • act (c' l) u ∈ Fil o.A
  rw [e]
  exact add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (h1 l)) (sum_mem fun i _ => h2 i)

theorem dualNumber_local (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

end GlobalTheory.HTCount.LieZFil

namespace GlobalTheory.HTCount


open LieZFil in
set_option maxHeartbeats 800000 in
theorem lieZ_mem_fil_and_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  intro p _ D R _ b N k _ t o₀ β ht o' m' z hz
  constructor
  · induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      exact sum_mem_fil β ht o₀ lam c hlam y'
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · have hbc := GlobalTheory.HTRealise.isBC_constMor o₀.ab
    suffices H : ∀ z ∈ lieZ o₀ β, hbc.bcMap z ∈ liftFil (epsDP k) m'.cart by
      refine ⟨hbc.bcMap z, H z hz, fun c => ?_⟩
      rw [(hbc.corr_iff.2 rfl) c]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hE : ∀ (x : D.O) (h : HdR o₀.A), crysToDR (epsDP k) m'.cart (hbc.bcMap (crysAct o₀ x h)) =
        GlobalTheory.HTSummand.crysAct (dp0 (DualNumber k)) (𝟙 _) o'.act x (crysToDR (epsDP k) m'.cart (hbc.bcMap h)) := by
      intro x h
      haveI := o₀.act.hom x
      haveI := o'.act.hom x
      have e1 : hbc.bcMap (crysAct o₀ x h) =
          push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act x) (hbc.bcMap h) := by
        rw [← hbc.corr_iff]
        exact GrpMor.Corr.push (m := constMor o₀.A) (constMor o₀.A) (o₀.act.act x) (o₀.act.act x) (by rfl)
          (hbc.corr_iff.2 rfl)
      have e2 := crysToDR_push (epsDP k) m'.cart m'.cart (o₀.act.act x) (o'.act.act x) (m'.act x).symm (hbc.bcMap h)
      exact (congrArg (crysToDR (epsDP k) m'.cart) e1).trans e2
    have hs : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
      rw [ht]; unfold spMap; rw [← Spec.map_comp]; rfl
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      have hlam' : ∀ i, ∑ l, algebraMap k (DualNumber k) (lam l) *
          ((algebraMap k (DualNumber k)).comp β) (b.t i (c l)) = 0 := fun i => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [RingHom.comp_apply, ← map_mul, ← map_sum, hlam i, map_zero]
      haveI : IsLocalRing (DualNumber k) := dualNumber_local k
      have key := sum_mem_fil ((algebraMap k (DualNumber k)).comp β) hs o' (fun l => algebraMap k _ (lam l)) c hlam'
        (crysToDR (epsDP k) m'.cart (hbc.bcMap y'))
      rw [liftFil, Submodule.mem_comap]
      convert key using 2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, hE, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, RingHom.comp_apply, map_intCast, RingHom.id_apply, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.HTCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFilStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  first | (exact @GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (exact GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (intros; apply GlobalTheory.HTCount.lieZ_mem_fil_and_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationSkew
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationSkew
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSkew


set_option maxHeartbeats 1000000 in
theorem skew_of_isFilLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  intro p _ D R _ b N k _ t o₀ φ hφ o' m' x _ y _ x₁ y₁ hx hy
  have HR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have HD : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g', hg'⟩ := GlobalTheory.KSGraph.exists_dim o'.A o'.ab
  obtain ⟨l₁, l₂⟩ := m'.sq
  have C : GlobalTheory.AbDual.CupSquare (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.A ⊗ o₀.A) :=
    GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 (isDPNilpotent_squareZero (SqExt.dual k).sq)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl o'.ab hg' o'.ab hg' m'.cart m'.cart
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
      (by
        calc
          _ = GlobalTheory.CechPic.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (GlobalTheory.CechPic.cls o₀.P o₀.isLB) := GlobalTheory.CechPic.cls_pull o₀.isLB _ _
          _ = _ := by rw [Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull o₀.isLB (constMor o₀.A) (constMor o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
  have van := GlobalTheory.BirigidLift.vanish_of_lift HR o'.ab hg' o'.ab hg' m'.cart m'.cart l₁ l₂ C o'.isLB o'.rig₁
    o'.rig₂ o₀.isLB (LBIso.symm m'.pol) hφ'
  have hm := GlobalTheory.HTRealise.isBC_constMor o₀.ab
  obtain ⟨xc, hxc⟩ := hm.exists x
  obtain ⟨yc, hyc⟩ := hm.exists y
  obtain ⟨x₁c, hx₁c⟩ := hm.exists x₁
  obtain ⟨y₁c, hy₁c⟩ := hm.exists y₁
  obtain ⟨d, hd, ed⟩ := hx
  obtain ⟨d', hd', ed'⟩ := hy
  have dx : d = xc + (DualNumber.eps : DualNumber k) • x₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hxc c, hx₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dy : d' = yc + (DualNumber.eps : DualNumber k) • y₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hyc c, hy₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have z : φ' d d' = 0 := van d hd d' hd'
  rw [dx, dy] at z
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    e' _ _ _ _ hxc hyc, e' _ _ _ _ hx₁c hyc, e' _ _ _ _ hxc hy₁c, e' _ _ _ _ hx₁c hy₁c] at z
  have z2 := congrArg TrivSqZeroExt.snd z
  simp [TrivSqZeroExt.algebraMap_eq_inl] at z2
  linear_combination z2

end GlobalTheory.HTSkew
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationSkewStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  first | (exact @GlobalTheory.HTSkew.skew_of_isFilLift) | (exact GlobalTheory.HTSkew.skew_of_isFilLift) | (intros; apply GlobalTheory.HTSkew.skew_of_isFilLift  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderHodgeEqKodairaSpencerGraph
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTNecessary

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀] {A' : Over (Sp (DualNumber k))} [GrpObj A']
  {i : A₀.left ⟶ A'.left} {h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i}

theorem isFilLift_add {x y x' y' : HdR A₀} (e : IsFilLift h x y) (e' : IsFilLift h x' y') :
    IsFilLift h (x + x') (y + y') := by
  obtain ⟨d, hd, e⟩ := e
  obtain ⟨d', hd', e'⟩ := e'
  refine ⟨d + d', add_mem hd hd', fun c ↦ ?_⟩
  rw [LinearMap.add_apply, e, e']
  ext <;> simp

theorem isFilLift_smul {x y : HdR A₀} (e : IsFilLift h x y) (r : k) :
    IsFilLift h (r • x) (r • y) := by
  obtain ⟨d, hd, e⟩ := e
  refine ⟨algebraMap k (DualNumber k) r • d, Submodule.smul_mem _ _ hd, fun c ↦ ?_⟩
  rw [LinearMap.smul_apply, e]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem isFilLift_zero : IsFilLift h (0 : HdR A₀) 0 :=
  ⟨0, zero_mem _, fun c ↦ by
    simp only [LinearMap.zero_apply, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]⟩

theorem isFilLift_push (f₀ : A₀ ⟶ A₀) (f : A' ⟶ A') [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ i)
    {x y : HdR A₀} (hxy : IsFilLift h x y) :
    IsFilLift h (push (dp0 k) (𝟙 _) f₀ x) (push (dp0 k) (𝟙 _) f₀ y) := by
  obtain ⟨d, hd, e'⟩ := hxy
  have hmem := push_mem_liftFil (epsDP k) h h f₀ f e hd
  refine ⟨_, hmem, fun c ↦ ?_⟩
  have k1 : GrpMor (dp0 k) (𝟙 _) A₀ (epsDP k) (DeRham.epsRed k) A₀
      (algebraMap k (DualNumber k)) (𝟙 _) f₀.left :=
    ⟨(constMor A₀).dp, (constMor A₀).base, (homMor (dp0 k) (𝟙 _) f₀).w,
      (homMor (dp0 k) (𝟙 _) f₀).mul⟩
  have e1 := GrpMor.pull_pull (constMor A₀) (homMor (epsDP k) _ f₀) k1 (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f₀) (constMor A₀) k1 (fun _ ↦ rfl) rfl c
  rw [push_apply]
  show d (primPull _ _ f₀ _) = _
  erw [primPull, e1, ← e2, e']
  rfl

theorem exists_isFilLift (hA' : IsAbelianScheme A') {x : HdR A₀} (hx : x ∈ Fil A₀) : ∃ y, IsFilLift h x y := by
  obtain ⟨g, hg⟩ := GlobalTheory.KSGraph.exists_dim A' hA'
  obtain ⟨v, ⟨y, hy, -⟩, -⟩ := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme GlobalTheory.T.abelianScheme_firstDeRham_structure h hA' hg x hx
  exact ⟨y, hy⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ φ hφ o' m'
  have hab₀ := o₀.ab
  have hab' := o'.ab
  have hL1 : ∀ x ∈ Fil o₀.A, ∃ y, IsFilLift m'.cart x y := fun x hx ↦ exists_isFilLift hab' hx
  have hG := GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart hab'
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Fil o₀.A)
  let bs := Module.Basis.ofVectorSpace k (Fil o₀.A)
  let f : Fil o₀.A →ₗ[k] HdR o₀.A := bs.constr k fun j ↦ (hL1 _ (bs j).2).choose
  have hf : ∀ x : Fil o₀.A, IsFilLift m'.cart x.1 (f x) := by
    intro x
    have hx : x ∈ Submodule.span k (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.constr_basis]
      exact (hL1 _ (bs j).2).choose_spec
    | zero => simpa using isFilLift_zero
    | add x y _ _ hx hy => simpa using isFilLift_add hx hy
    | smul r x _ hx => simpa using isFilLift_smul hx r
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := f ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hg : ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := fun x hx ↦ by
    have : Submodule.linearProjOfIsCompl _ _ hC x = ⟨x, hx⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩
    simpa [g, this] using hf ⟨x, hx⟩
  refine ⟨g, ⟨fun a x hx ↦ ?_, fun z hz ↦ ?_, fun x hx y hy ↦ ?_⟩, hg⟩
  · haveI := o₀.act.hom a
    haveI := o'.act.hom a
    have hax : GlobalTheory.HTCount.crysAct o₀ a x ∈ Fil o₀.A := by
      rw [GlobalTheory.HTCount.crysAct_apply]; exact push_mem_Fil _ hx
    have e1 : IsFilLift m'.cart (GlobalTheory.HTCount.crysAct o₀ a x) (GlobalTheory.HTCount.crysAct o₀ a (g x)) := by
      rw [GlobalTheory.HTCount.crysAct_apply]
      exact isFilLift_push (o₀.act.act a) (o'.act.act a) (m'.act a).symm (hg x hx)
    exact (hG _ hax _ _ e1).1 (hg _ hax)
  · obtain ⟨hz₀, hz⟩ := GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil p D R b N k t o₀ β hβ o' m' z hz
    simpa using (hG _ hz₀ _ _ hz).1 (hg _ hz₀)
  · exact GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew p D R b N k t o₀ φ hφ o' m' x hx y hy _ _ (hg x hx) (hg y hy)

end GlobalTheory.HTNecessary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderHodgeEqKodairaSpencerGraphStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  first | (exact @GlobalTheory.HTNecessary.main) | (exact GlobalTheory.HTNecessary.main) | (intros; apply GlobalTheory.HTNecessary.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, t = spMap β := ⟨(Spec.preimage t).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k t o₀
  obtain ⟨f, hfKS, huniq⟩ := GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim p D R b N hN hNp k t o₀ β hβ φ hφ
  refine ⟨f, fun j => GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k t o₀ β hβ φ hφ (f j) (hfKS j), fun o' m' => ?_⟩
  obtain ⟨g, hgKS, hg⟩ := GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph p D R b N hN hNp k t o₀ β hβ φ hφ o' m'
  obtain ⟨c, hc, hcu⟩ := huniq g hgKS
  refine ⟨c, fun x hx => ?_, fun c' hc' => hcu c' fun x hx => ?_⟩
  · refine (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).2 ?_
    rw [← neg_sub]; exact neg_mem (hc x hx)
  · have := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).1 (hc' x hx)
    rw [← neg_sub]; exact neg_mem this

end GlobalTheory.HTCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCountStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  first | (exact @GlobalTheory.HTCount.count) | (exact GlobalTheory.HTCount.count) | (intros; apply GlobalTheory.HTCount.count  <;> assumption)
end

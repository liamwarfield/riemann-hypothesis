module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PoincareLelong
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma inter_inr_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (_i : DecidableEq (β ⊕ₗ κ))
    (b : Finset β) (L : Finset κ) :
    (uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = L.card := by
  have h : uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding =
      L.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with i | l <;> simp [uni, inrE]
  rw [h, Finset.card_map]

private lemma inl_not_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (i : β) :
    (inlE i : β ⊕ₗ κ) ∉ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp [inlE, inrE]

private lemma inr_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp

theorem UpperTheory.Gal.productCup_of_system.localOne_of_gl1 :
    FiltrationBoundaryCriterion → ColQEx → WdUni → L1 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c hc hd hB
  have e : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w c ∅ ∅).2.2.2.2
  have eL : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w c b L).2.1
  have eR : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w c b L).2.2.1
  have eC : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    have := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rwa [e s] at this
  have hS : ∀ (_i : DecidableEq (β ⊕ₗ κ)) (s : Finset (β ⊕ₗ κ)),
      (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := fun i s => by
    have := inter_inr_card i (lft s) (rgt s)
    rwa [e s] at this
  have hy : ∀ b : Finset β, (b.card : ℤ) = n - d →
      ∃ y ∈ (colA A w b).C (d - 1), (colA A w b).D y = col c b := fun b hb => by
    obtain ⟨y, hy, h⟩ := hB b hb
    exact ⟨y, hy, h⟩
  let yb : Finset β → Finset κ → E := fun b => if h : (b.card : ℤ) = n - d then (hy b h).choose else 0
  have hyb : ∀ b, (b.card : ℤ) = n - d → yb b ∈ (colA A w b).C (d - 1) ∧ (colA A w b).D (yb b) = col c b := by
    intro b hb
    simp only [yb, dif_pos hb]
    exact (hy b hb).choose_spec
  have hy0 : ∀ b, ¬ (b.card : ℤ) = n - d → yb b = 0 := by
    intro b hb
    simp only [yb, dif_neg hb]
  let y : Finset (β ⊕ₗ κ) → E := fun s => ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s)
  have hmem : ∀ b, (b.card : ℤ) = n - d → ∀ L, yb b L ∈ (if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := by
    intro b hb L
    have h : yb b ∈ Submodule.pi Set.univ
      (fun L : Finset κ => if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := (hyb b hb).1
    exact (Submodule.mem_pi.1 h) L (Set.mem_univ _)
  have hz : ∀ s, ¬ (((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1) → y s = 0 := by
    intro s hs
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have hL : ¬ ((rgt s).card : ℤ) = d - 1 := fun h => hs ⟨hb, h⟩
      have h1 := hmem _ hb (rgt s)
      rw [if_neg hL, Submodule.mem_bot] at h1
      simp only [y, h1, smul_zero]
    · simp only [y, hy0 _ hb, Pi.zero_apply, smul_zero]
  have hcC : ∀ s : Finset (β ⊕ₗ κ), ¬ (s.card : ℤ) = n → c s = 0 := by
    intro s hs
    have h : c ∈ Submodule.pi Set.univ
      (fun s : Finset (β ⊕ₗ κ) => if (s.card : ℤ) = n then A s else ⊥) := hc.1
    have h1 := (Submodule.mem_pi.1 h) s (Set.mem_univ _)
    rwa [if_neg hs, Submodule.mem_bot] at h1
  refine hG (β ⊕ₗ κ) E A w (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) d n hW
    (hC β κ E A w d hK) c hc ?_ ⟨y, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : d < ((rgt s).card : ℤ) := by
      rw [hS _ s] at hs
      exact not_le.1 hs
    have := hd (lft s) (rgt s) hs'
    rwa [e s] at this
  · refine Submodule.mem_pi.2 fun s _ => ?_
    by_cases h : ((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1
    · have hcard : (s.card : ℤ) = n - 1 := by
        rw [eC s]; push_cast; omega
      have h1 := hmem _ h.1 (rgt s)
      rw [if_pos h.2, e s] at h1
      show y s ∈ (if (s.card : ℤ) = n - 1 then A s else ⊥)
      rw [if_pos hcard]
      exact zsmul_mem h1 _
    · rw [hz s h]
      exact zero_mem _
  · intro s hs
    rw [hS _ s] at hs
    exact hz s fun h => hs h.2
  · intro s hs
    rw [hS _ s] at hs
    conv_lhs => rw [← e s]
    rw [(hU β κ E _ y (lft s) (rgt s)).1]
    have h0 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun i : β => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inlE i)) = fun _ => 0 := by
      intro _i
      funext i
      simp only [wOn, if_neg (inl_not_mem i)]
    have h1 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun l : κ => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inrE l)) = fun l => w (inrE l) := by
      intro _i
      funext l
      simp only [wOn, if_pos (inr_mem l)]
    have h2 : (fun L' : Finset κ => y (uni (lft s) L')) = ((-1 : ℤ) ^ (lft s).card) • yb (lft s) := by
      funext L'
      simp only [y, eL, eR, Pi.smul_apply]
    have h3 : wd (fun _ : β => (0 : Module.End ℂ E)) (fun b' => y (uni b' (rgt s))) (lft s) = 0 := by
      simp [wd]
    rw [h0 _, h1 _, h3, zero_add, h2, map_zsmul, Pi.smul_apply, smul_smul, ← mul_pow]
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have h4 := congrFun (hyb _ hb).2 (rgt s)
      have h5 : wd (fun l : κ => w (inrE l)) (yb (lft s)) (rgt s) = c s := by
        have : col c (lft s) (rgt s) = c s := by
          show c (uni (lft s) (rgt s)) = c s
          rw [e s]
        rw [← this]
        exact h4
      rw [h5]
      simp
    · rw [hy0 _ hb, hcC s (by rw [eC s]; push_cast; omega)]
      simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoInjectiveOfGl1
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma exists_of_mem_sm_range {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) (x : E)
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ m : Fin d → E, (∀ j, m j ∈ M) ∧ x = ∑ j, act (f j) (m j) := by
  classical
  let L : (Fin d → M) →ₗ[ℂ] E :=
    ∑ j, ((act (f j) : E →ₗ[ℂ] E) ∘ₗ M.subtype ∘ₗ (LinearMap.proj j : (Fin d → M) →ₗ[ℂ] M))
  have hL : ∀ v, L v = ∑ j, act (f j) (v j : E) := by
    intro v
    simp [L, LinearMap.sum_apply]
  have hle : sm act M (Set.range f) ≤ LinearMap.range L := by
    refine iSup₂_le ?_
    rintro _ ⟨j, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨Pi.single j ⟨m, hm⟩, ?_⟩
    rw [hL, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  obtain ⟨v, rfl⟩ := hle hx
  exact ⟨fun j => (v j : E), fun j => (v j).2, hL v⟩

theorem UpperTheory.Gal.productCup_of_system.koszulTwoInjective_of_gl1 :
    FiltrationBoundaryCriterion → SubQEx → KoszulBoundaryOfComponentMemIdeal := by
  intro gl1 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hKE c hc hsm
  classical
  obtain ⟨m, hm, hcm⟩ := exists_of_mem_sm_range act M (fun j => r (e j)) _ hsm
  have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
    refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
    show act (r i) * act (r j) = act (r j) * act (r i)
    rw [← map_mul, ← map_mul, mul_comm]
  have hQ := subq S E act κ M r d e hKE
  have hQc : (img e).card = d := by simp [img]
  have hmem : ∀ j, e j ∈ img e := fun j => by simp [img]
  have hcz : ∀ s : Finset κ, (s.card : ℤ) ≠ d → c s = 0 := by
    intro s hs
    have h := hc.1 s (Set.mem_univ s)
    simpa [hs] using h
  have hcard : ∀ j, (((img e).erase (e j)).card : ℤ) = (d : ℤ) - 1 := by
    intro j
    have := j.pos
    rw [Finset.card_erase_of_mem (hmem j), hQc]
    omega
  have hinj : ∀ i j, (img e).erase (e i) = (img e).erase (e j) → i = j := by
    intro i j h
    by_contra hij
    have hne : e i ≠ e j := fun h' => hij (e.injective h')
    have h1 : e i ∈ (img e).erase (e j) := Finset.mem_erase.mpr ⟨hne, hmem i⟩
    rw [← h] at h1
    exact (Finset.notMem_erase _ _) h1
  let y : Finset κ → E := fun s =>
    ∑ j, if s = (img e).erase (e j) then GlobalTheory.cubeSign (img e) (e j) • m j else 0
  have hyv : ∀ j, y ((img e).erase (e j)) = GlobalTheory.cubeSign (img e) (e j) • m j := by
    intro j
    show (∑ i, if (img e).erase (e j) = (img e).erase (e i) then _ else _) = _
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hinj _ _ h).symm]
    · simp
  have hy0 : ∀ s, (∀ j, s ≠ (img e).erase (e j)) → y s = 0 := by
    intro s hs
    exact Finset.sum_eq_zero fun j _ => if_neg (hs j)
  have hycard : ∀ s : Finset κ, (s.card : ℤ) ≠ (d : ℤ) - 1 → y s = 0 := by
    intro s hs
    refine hy0 s fun j h => hs ?_
    rw [h, hcard]
  refine gl1 κ E (fun _ => M) (fun l => act (r l)) (img e) d d hW hQ c hc ?_ ?_
  · intro s hs
    exfalso
    apply hs
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := img e))
    rw [hQc] at this
    exact_mod_cast this
  · refine ⟨y, ?_, ?_, ?_⟩
    · intro s _
      show y s ∈ if (s.card : ℤ) = (d : ℤ) - 1 then M else ⊥
      split_ifs with h
      · refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs
        · exact zsmul_mem (hm j) _
        · exact M.zero_mem
      · rw [hycard s h]
        exact Submodule.zero_mem _
    · intro s hs
      refine hy0 s fun j h => hs ?_
      subst h
      rw [Finset.inter_eq_left.mpr (Finset.erase_subset _ _), hcard]
    · intro s hs
      have hsub : img e ⊆ s := by
        have h1 : (s ∩ img e) = img e := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          rw [hQc]
          exact_mod_cast hs.ge
        rw [← h1]
        exact Finset.inter_subset_left
      have hwd : ∀ t : Finset κ, wd (wOn (img e) fun l => act (r l)) y t =
          ∑ i ∈ t, GlobalTheory.cubeSign t i • (wOn (img e) (fun l => act (r l)) i) (y (t.erase i)) := by
        intro t
        simp [wd, LinearMap.sum_apply]
      rw [hwd]
      by_cases hsQ : s = img e
      · subst hsQ
        rw [hcm]
        have hsum : ∀ F : κ → E, ∑ i ∈ img e, F i = ∑ j, F (e j) := fun F =>
          Finset.sum_map _ _ _
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hw : wOn (img e) (fun l => act (r l)) (e j) = act (r (e j)) := if_pos (hmem j)
        have hsq : GlobalTheory.cubeSign (img e) (e j) * GlobalTheory.cubeSign (img e) (e j) = 1 := by
          rw [GlobalTheory.cubeSign, ← mul_pow]
          simp
        rw [hw, hyv j, map_zsmul, smul_smul, hsq, one_smul]
      · have hlt : img e ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hsQ h.symm⟩
        have hgt : d < s.card := by
          have := Finset.card_lt_card hlt
          rwa [hQc] at this
        rw [hcz s (by omega)]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hycard (s.erase i) ?_]
        · simp
        · rw [Finset.card_erase_of_mem hi]
          omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WeightInverseContinuity
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma card_img {κ : Type} [LinearOrder κ] {d : ℕ} (e : Fin d ↪o κ) : (img e).card = d := by
  simp [img]

private lemma detC_img {S κ : Type} [CommRing S] [LinearOrder κ] {d : ℕ} (ρ : κ → Fin d → S) (e : Fin d ↪o κ)
    (A : Matrix (Fin d) (Fin d) S) (hA : ∀ a, ρ (e a) = A a) : detC ρ (img e) = A.det := by
  have h := card_img e
  have hu : e = (img e).orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique' h (fun x => by simp [img])
  rw [detC, dite_eq_left h]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [← hu, hA]

private lemma detC_mem {S κ : Type} [CommRing S] [Algebra ℂ S] [LinearOrder κ] {d : ℕ} (R : Subalgebra ℂ S)
    (ρ : κ → Fin d → S) (h : ∀ l b, ρ l b ∈ R) (s : Finset κ) : detC ρ s ∈ R := by
  unfold detC
  split_ifs with hs
  · rw [Matrix.det_apply']
    exact R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => h _ _)
  · exact R.zero_mem

private lemma core (hDet : Det) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hKS : KSub) (hWB : WdBasic)
    {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
    {κ κ0 : Type} [LinearOrder κ] [Fintype κ] [LinearOrder κ0] [Fintype κ0]
    (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) {d : ℕ} (ι : κ0 ↪o κ) (e0 e0' : Fin d ↪o κ0)
    (N : Matrix (Fin d) (Fin d) S) (ρ : κ0 → Fin d → S)
    (h1 : ∀ j, ρ (e0 j) = Pi.single j 1) (h2 : ∀ a, ρ (e0' a) = N a) (hρ : ∀ l b, ρ l b ∈ R)
    (hrel : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)))
    (hSt : Stab act R M) (hr : ∀ l, r l ∈ R)
    (hKE : KE (kos act M fun j => r (ι (e0 j))) d) (c : Finset κ → E) (hc : c ∈ (kos act M r).Z d) :
    c ((img e0').map ι.toEmbedding) - act N.det (c ((img e0).map ι.toEmbedding)) ∈
      sm act M (Set.range fun j => r (ι (e0 j))) := by
  have hcC : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥) := fun s =>
    (Submodule.mem_inf.1 hc).1 s (Set.mem_univ _)
  have hcD : wd (fun l => act (r l)) c = 0 := (Submodule.mem_inf.1 hc).2
  obtain ⟨m, hm⟩ : ∃ m, m = c ((img e0).map ι.toEmbedding) := ⟨_, rfl⟩
  rw [← hm]
  have hmM : m ∈ M := by
    have := hcC ((img e0).map ι.toEmbedding)
    rw [if_pos (by simp [card_img])] at this
    rwa [hm]
  have hZ0 : (fun t : Finset κ0 => c (t.map ι.toEmbedding)) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · have := hcC (s.map ι.toEmbedding)
      simpa using this
    · show wd (fun l => act (r (ι l))) (fun t : Finset κ0 => c (t.map ι.toEmbedding)) = 0
      funext s
      have := (hWB κ E (fun _ => M) (fun l => act (r l))).2.2.2.2.2 κ0 ι c s
      rw [this, hcD]; rfl
  have hZ' : (fun s : Finset κ0 => act (detC ρ s) m) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · show act (detC ρ s) m ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥)
      split_ifs with hs
      · exact hSt _ (detC_mem R ρ hρ s) m hmM
      · have : s.card ≠ d := fun h => hs (by rw [h])
        simp [detC, this]
    · show wd (fun l => act (r (ι l))) (fun s : Finset κ0 => act (detC ρ s) m) = 0
      have := hDet S E act κ0 d ρ (fun b => r (ι (e0 b))) m
      rwa [show (fun l => act (∑ b, ρ l b * r (ι (e0 b)))) = fun l => act (r (ι l)) from
        funext fun l => by rw [hrel l]] at this
  have hB := hK2 S E act κ0 R M (fun l => r (ι l)) d e0 hSt (fun l => hr _) hKE _
    (Submodule.sub_mem _ hZ0 hZ') (by
      have h1' : detC ρ (img e0) = 1 := by
        rw [detC_img ρ e0 1 (fun a => by rw [h1 a]; ext b; simp [Matrix.one_apply, Pi.single_apply, eq_comm])]
        simp
      simp only [Pi.sub_apply, h1', map_one, Module.End.one_apply, ← hm, sub_self]
      exact Submodule.zero_mem _)
  have hval := (hKS S E act κ0 R M (fun l => r (ι l)) hSt (fun l => hr _)).2 d _ hB (img e0')
  have hdet : detC ρ (img e0') = N.det := detC_img ρ e0' N h2
  simp only [Pi.sub_apply, hdet] at hval
  refine (?_ : sm act M (Set.range fun l => r (ι l)) ≤ sm act M (Set.range fun j => r (ι (e0 j)))) hval
  unfold sm
  refine iSup₂_le ?_
  rintro _ ⟨l, rfl⟩ _ ⟨x, hx, rfl⟩
  show act (r (ι l)) x ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hrel l, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [mul_comm, map_mul, Module.End.mul_apply]
  exact (le_iSup₂_of_le (f := fun (t : S) (_ : t ∈ Set.range fun j => r (ι (e0 j))) => M.map (act t))
    (r (ι (e0 b))) ⟨b, rfl⟩ le_rfl) (Submodule.mem_map_of_mem (hSt _ (hρ l b) x hx))

theorem UpperTheory.Gal.productCup_of_system.koszulThree_of_det :
    Det → KoszulBoundaryOfComponentMemIdeal → KSub → WdBasic → K3 := by
  intro hDet hK2 hKS hWB S E _ _ _ _ act κ _ _ R M r d e e' N hSt hr hN hrel hdis hKE c hc
  classical
  have hmemL : ∀ j, e j ∈ img e ∪ img e' := fun j => Finset.mem_union_left _ (by simp [img])
  have hmemR : ∀ j, e' j ∈ img e ∪ img e' := fun j => Finset.mem_union_right _ (by simp [img])
  let ι : {l // l ∈ img e ∪ img e'} ↪o κ := OrderEmbedding.subtype _
  let e0 : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e j, hmemL j⟩) fun a b h => e.strictMono h
  let e0' : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e' j, hmemR j⟩) fun a b h => e'.strictMono h
  let ρ : {l // l ∈ img e ∪ img e'} → Fin d → S := fun l =>
    if h : ∃ j, e j = l.1 then Pi.single h.choose 1 else if h' : ∃ a, e' a = l.1 then N h'.choose else 0
  have h1 : ∀ j, ρ (e0 j) = Pi.single j 1 := fun j => by
    have hex : ∃ i, e i = (e0 j).1 := ⟨j, rfl⟩
    have : hex.choose = j := e.injective hex.choose_spec
    simp only [ρ]
    rw [dite_eq_left hex, this]
  have h2 : ∀ a, ρ (e0' a) = N a := fun a => by
    have hn : ¬ ∃ j, e j = (e0' a).1 := fun ⟨j, hj⟩ => hdis a j hj.symm
    have hex : ∃ i, e' i = (e0' a).1 := ⟨a, rfl⟩
    have : hex.choose = a := e'.injective hex.choose_spec
    simp only [ρ]
    rw [dite_eq_right hn, dite_eq_left hex, this]
  have hρ : ∀ l b, ρ l b ∈ R := fun l b => by
    simp only [ρ]
    split_ifs with h h'
    · rw [Pi.single_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · exact hN _ _
    · exact R.zero_mem
  have hrel' : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)) := fun l => by
    obtain ⟨l, hl⟩ := l
    rcases Finset.mem_union.1 hl with h | h
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 h
      have := h1 j
      change r (e j) = ∑ b, ρ (e0 j) b * r (e b)
      rw [this]
      simp [Pi.single_apply]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h
      have := h2 a
      change r (e' a) = ∑ b, ρ (e0' a) b * r (e b)
      rw [this]
      exact hrel a
  have key := core hDet hK2 hKS hWB act R M r ι e0 e0' N ρ h1 h2 hρ hrel' hSt hr hKE c hc
  have hi : (img e0).map ι.toEmbedding = img e := by
    ext x; simp [img, ι, e0]
  have hi' : (img e0').map ι.toEmbedding = img e' := by
    ext x; simp [img, ι, e0']
  rw [hi, hi'] at key
  exact key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FiltrationCocycleLiftCriterionOfWdBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma mem_acxC {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c : Finset σ → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  simp [acx, Submodule.mem_pi]

private lemma wd_wOn_mem {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (h : WOk A w) (P : Finset σ) {n : ℤ} {c : Finset σ → E} (hc : c ∈ (acx A w).C n) :
    wd (wOn P w) c ∈ (acx A w).C (n + 1) := by
  rw [mem_acxC] at hc ⊢
  intro s
  rw [wd_apply']
  by_cases hs : (s.card : ℤ) = n + 1
  · rw [if_pos hs]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_
    have hcard : ((s.erase i).card : ℤ) = n := by
      have := Finset.card_erase_add_one hi
      omega
    have hmem := hc (s.erase i)
    rw [if_pos hcard] at hmem
    unfold wOn
    split_ifs
    · have := h.2 (s.erase i) i (by simp) _ hmem
      rwa [Finset.insert_erase hi] at this
    · rw [LinearMap.zero_apply]
      exact Submodule.zero_mem _
  · rw [if_neg hs, Submodule.mem_bot]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : ¬ ((s.erase i).card : ℤ) = n := by
      have := Finset.card_erase_add_one hi
      omega
    have hmem := hc (s.erase i)
    rw [if_neg hcard, Submodule.mem_bot] at hmem
    rw [hmem, map_zero, smul_zero]

private lemma wd_compl_lev [Fintype σ] {Q : Finset σ} {w : σ → Module.End ℂ E} {m : ℤ}
    {c : Finset σ → E} (h : Lev Q (· = m) c) : Lev Q (· = m) (wd (wOn Qᶜ w) c) := by
  intro s hs
  rw [wd_apply']
  refine Finset.sum_eq_zero fun i hi => ?_
  unfold wOn
  split_ifs with hiQ
  · rw [Finset.mem_compl] at hiQ
    have hQ : (s.erase i) ∩ Q = s ∩ Q := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx⟩, hxQ⟩
        exact ⟨hx, hxQ⟩
      · rintro ⟨hx, hxQ⟩
        exact ⟨⟨fun hxi => hiQ (by rw [← hxi]; exact hxQ), hx⟩, hxQ⟩
    rw [h (s.erase i) (by rw [hQ]; exact hs), map_zero, smul_zero]
  · rw [LinearMap.zero_apply, smul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.productCup_of_system.filtrationCocycleLiftCriterion_of_wdBasic :
    WdBasic → FiltrationCocycleLiftCriterion := by
  rintro hB σ E _ _ _ _ A w Q d n hW hQE c0 hc0 hl0 hq0 ⟨y, hy, hly, hdy⟩
  have hcw : ∀ P P' : Finset σ, ∀ i j, Commute (wOn P w i) (wOn P' w j) := by
    intro P P' i j
    unfold wOn
    split_ifs
    all_goals first
      | exact hW.1 i j
      | exact Commute.zero_right _
      | exact Commute.zero_left _
  have hsplit : ∀ x, wd w x = wd (wOn Q w) x + wd (wOn Qᶜ w) x := by
    intro x
    have hw : w = wOn Q w + wOn Qᶜ w := by
      funext i
      by_cases hi : i ∈ Q <;> simp [wOn, hi]
    conv_lhs => rw [hw]
    rw [(hB σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w), LinearMap.add_apply]
  have hRR : ∀ x, wd (wOn Qᶜ w) (wd (wOn Qᶜ w) x) = 0 := (hB σ E A (wOn Qᶜ w)).1 (hcw Qᶜ Qᶜ)
  have hQR : ∀ x, wd (wOn Q w) (wd (wOn Qᶜ w) x) + wd (wOn Qᶜ w) (wd (wOn Q w) x) = 0 :=
    (hB σ E A (wOn Q w)).2.2.2.1 (wOn Qᶜ w) (hcw Q Qᶜ) (fun i => by by_cases hi : i ∈ Q <;> simp [wOn, hi])
  have levZero : ∀ (m : ℤ) (x : Finset σ → E), m < 0 → Lev Q (· = m) x → x = 0 := by
    intro m x hm hx
    funext s
    exact hx s (fun h => by
      have h' : (((s ∩ Q).card : ℕ) : ℤ) = m := h
      omega)
  have key : ∀ j : ℕ, ∀ m : ℤ, m < j → m < d → ∀ ck yk : Finset σ → E,
      ck ∈ (acx A w).C n → Lev Q (· < d) (ck - c0) → yk ∈ (acx A w).C n → Lev Q (· = m) yk →
      wd w ck = -wd (wOn Qᶜ w) yk → wd (wOn Q w) (wd (wOn Qᶜ w) yk) = 0 →
      ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c0) := by
    intro j
    induction j with
    | zero =>
      intro m hm _ ck yk hck hlk _ hly hd _
      have hy0 := levZero m yk (by exact_mod_cast hm) hly
      refine ⟨ck, ?_, hlk⟩
      show ck ∈ (acx A w).C n ⊓ LinearMap.ker (acx A w).D
      refine Submodule.mem_inf.2 ⟨hck, LinearMap.mem_ker.2 ?_⟩
      show wd w ck = 0
      rw [hd, hy0, map_zero, neg_zero]
    | succ j ih =>
      intro m hm hmd ck yk hck hlk hyk hly hd hqr
      have hmem : -wd (wOn Qᶜ w) yk ∈ (acx A w).C (n + 1) :=
        Submodule.neg_mem _ (wd_wOn_mem hW Qᶜ hyk)
      have hlev : Lev Q (· = m) (-wd (wOn Qᶜ w) yk) := by
        intro s hs
        rw [Pi.neg_apply, wd_compl_lev hly s hs, neg_zero]
      have hdq : wd (wOn Q w) (-wd (wOn Qᶜ w) yk) = 0 := by rw [map_neg, hqr, neg_zero]
      obtain ⟨y', hy', hly', hdy'⟩ := hQE (n + 1) m hmd _ hmem hlev hdq
      rw [add_sub_cancel_right] at hy'
      refine ih (m - 1) (by push_cast at hm; omega) (by omega) (ck - y') y'
        (Submodule.sub_mem _ hck hy') ?_ hy' hly' ?_ ?_
      · intro s hs
        have h1 := hlk s hs
        have h2 := hly' s (fun h => hs (by
          have h' : (((s ∩ Q).card : ℕ) : ℤ) = m - 1 := h
          show (((s ∩ Q).card : ℕ) : ℤ) < d
          omega))
        simp only [Pi.sub_apply] at h1 ⊢
        rw [h2, sub_zero]
        exact h1
      · rw [map_sub, hd, hsplit y', hdy']
        abel
      · have := hQR y'
        rw [hdy', map_neg, hRR, neg_zero, add_zero] at this
        exact this
  refine key d.toNat (d - 1) (by have := Int.self_le_toNat d; omega) (by omega) (c0 - y) y
    (Submodule.sub_mem _ hc0 hy) ?_ hy hly ?_ ?_
  · intro s hs
    have h2 := hly s (fun h => hs (by
      have h' : (((s ∩ Q).card : ℕ) : ℤ) = d - 1 := h
      show (((s ∩ Q).card : ℕ) : ℤ) < d
      omega))
    simp only [Pi.sub_apply]
    rw [h2]
    abel
  · rw [map_sub, hsplit c0, hsplit y, hq0, hdy]
    abel
  · have := hQR y
    rw [hdy, hRR, add_zero] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RowMuNull
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma card_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ) :
    (uni I J).card = I.card + J.card := by
  simp [uni]

private lemma mem_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ)
    (t : β ⊕ₗ κ) : t ∈ uni I J ↔ (∃ i ∈ I, t = toLex (Sum.inl i)) ∨ ∃ l ∈ J, t = toLex (Sum.inr l) := by
  simp only [uni, Finset.mem_map, Finset.mem_disjSum, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨Sum.inl i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
    · exact ⟨Sum.inr l, Or.inr ⟨l, hl, rfl⟩, rfl⟩

private lemma detC_eq {κ : Type} [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (s : Finset κ)
    (f : Fin p → κ) (hc : s.card = p) (hs : ∀ x, f x ∈ s) (hf : StrictMono f) :
    detC ρ s = (Matrix.of fun a b => ρ (f a) b).det := by
  unfold detC
  rw [dite_eq_left hc, Finset.orderEmbOfFin_unique hc hs hf]

private lemma rowMu_inr (l : Mi d) (m : Fin (d + 1)) : T.rowMu (toLex (Sum.inr l)) m =
    (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
      if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0 := rfl

private lemma rowMu_inl (i m : Fin (d + 1)) : T.rowMu (toLex (Sum.inl i)) m =
    (Pi.single i 1 : Fin (d + 1) → S) m := rfl

private lemma rowMu_sum (t : Fin (d + 1) ⊕ₗ Mi d) :
    ∑ b, T.rowMu t b * (1 : Fin (d + 1) → S) b = app (fun _ => (1 : S)) T.mu t := by
  obtain ⟨t, rfl⟩ := toLex.surjective t
  rcases t with i | l
  · simp [rowMu_inl, app]
  · simp only [rowMu_inr, Pi.one_apply, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl

private lemma rowMu_null (l : Mi d) :
    ∑ m, T.rowMu (toLex (Sum.inr l)) m * ((T.Y m * (T.X m)⁻¹ : Sˣ) : S) = 0 := by
  simp only [rowMu_inr, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Units.val_mul]
  have h1 : ((T.X (ofLex l).1 : Sˣ) : S) * (((T.X (ofLex l).1)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  have h2 : ((T.X (ofLex l).2 : Sˣ) : S) * (((T.X (ofLex l).2)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  linear_combination ((T.Y (ofLex l).1 : S) * (T.Y (ofLex l).2 : S)) * (h1 - h2)

private lemma detC_left (L : Finset (Mi d)) : detC T.rowMu (uni ∅ L) = 0 := by
  unfold detC
  split_ifs with h
  · set A : Matrix (Fin (d + 1)) (Fin (d + 1)) S :=
      Matrix.of fun a b => T.rowMu ((uni ∅ L).orderEmbOfFin h a) b with hA
    have hAv : A.mulVec (fun m => ((T.Y m * (T.X m)⁻¹ : Sˣ) : S)) = 0 := by
      funext a
      have hmem : (uni ∅ L).orderEmbOfFin h a ∈ uni ∅ L := Finset.orderEmbOfFin_mem _ _ _
      rw [mem_uni] at hmem
      rcases hmem with ⟨i, hi, _⟩ | ⟨l, _, hl⟩
      · simp at hi
      · simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, hl, Pi.zero_apply]
        exact rowMu_null T l
    have h0 := congrArg A.adjugate.mulVec hAv
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h0
    have h1 := congrFun h0 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    exact (Units.mul_left_eq_zero (T.Y 0 * (T.X 0)⁻¹)).1 h1
  · rfl

private lemma detC_univ : detC T.rowMu (uni Finset.univ ∅) = 1 := by
  rw [detC_eq T.rowMu _ (fun a => toLex (Sum.inl a)) (by simp [card_uni])
    (fun x => (mem_uni _ _ _).2 (Or.inl ⟨x, Finset.mem_univ _, rfl⟩))
    (fun a b h => Sum.Lex.inl_strictMono h)]
  have : (Matrix.of fun a b => T.rowMu (toLex (Sum.inl a)) b) = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) S) := by
    ext a b
    simp [rowMu_inl, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]

private lemma detC_top : detC T.rowMu (uni {0} (img (dj 0))) =
    (∏ l : Fin d, (T.X l.succ : S)) * (T.Y 0 : S) ^ d := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Mi d :=
    Fin.cons (toLex (Sum.inl 0)) fun l => toLex (Sum.inr (dj 0 l))
  have hf0 : f 0 = toLex (Sum.inl 0) := rfl
  have hfs : ∀ l : Fin d, f l.succ = toLex (Sum.inr (dj 0 l)) := fun _ => rfl
  have hmono : StrictMono f := by
    intro a b h
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ b => rw [hf0, hfs]; exact Sum.Lex.inl_lt_inr _ _
    | succ a =>
      induction b using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ b =>
        rw [hfs, hfs]
        exact Sum.Lex.inr_strictMono ((dj 0).strictMono (Fin.succ_lt_succ_iff.1 h))
  have hmem : ∀ x, f x ∈ uni {0} (img (dj 0)) := by
    intro x
    induction x using Fin.cases with
    | zero => exact (mem_uni _ _ _).2 (Or.inl ⟨0, by simp, rfl⟩)
    | succ l => exact (mem_uni _ _ _).2 (Or.inr ⟨dj 0 l, by simp [img], rfl⟩)
  rw [detC_eq T.rowMu _ f (by simp [card_uni, img, add_comm]) hmem hmono]
  have hrow : ∀ (l : Fin d) (m : Fin (d + 1)), T.rowMu (f l.succ) m =
      (if m = l.succ then (T.X m * T.Y 0 : S) else 0) -
        if m = 0 then (T.X m * T.Y l.succ : S) else 0 := by
    intro l m
    have e1 : (ofLex (dj (0 : Fin (d + 1)) l)).1 = l.succ := by simp [dj]
    have e2 : (ofLex (dj (0 : Fin (d + 1)) l)).2 = 0 := rfl
    rw [hfs, rowMu_inr, e1, e2]
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp only [Matrix.of_apply, hf0, rowMu_inl, Pi.single_eq_same, one_mul, hrow]
    simp [Finset.prod_mul_distrib, Fin.succ_ne_zero]
  · intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.of_apply]
    induction i using Fin.cases with
    | zero =>
      rw [hf0, rowMu_inl]
      simp [Pi.single_apply, (Fin.pos_iff_ne_zero.1 hij')]
    | succ l =>
      rw [hrow]
      have h1 : j ≠ l.succ := ne_of_gt hij'
      have h2 : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [h1, h2]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.thMu_of :
    Det → ThMu := by
  intro hDet d S E _ _ _ _ T
  refine ⟨?_, detC_left T, detC_univ T, detC_top T⟩
  have h := hDet S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Mi d) (d + 1) T.rowMu 1 1
  simp only [rowMu_sum] at h
  have e : (fun s => (Algebra.lmul ℂ S) (detC T.rowMu s) (1 : S)) = detC T.rowMu := by
    funext s
    simp
  rwa [e] at h
end

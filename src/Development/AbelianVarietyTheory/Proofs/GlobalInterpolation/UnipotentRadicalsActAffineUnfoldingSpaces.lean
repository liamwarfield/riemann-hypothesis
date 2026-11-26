module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces

variable {F : Type} [Field F] {n' c' n c : ℕ}

theorem hom_ext {a b : ℕ} {x y : (Fin a → F) →ₗ[F] (Fin b → F)}
    (h : ∀ s l, x (Pi.single s 1) l = y (Pi.single s 1) l) : x = y := by
  ext s l
  simpa using h s l

noncomputable def linPart (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) :
    (Loc.FC n' c' n c → F) →ₗ[F] ((Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) where
  toFun t := Loc.xx1 xj t - Loc.xx1 xj 0
  map_add' t u := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply, Pi.add_apply, linearMap_unfolding_apply_single]
    split_ifs <;> simp
  map_smul' a t := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, linearMap_unfolding_apply_single, RingHom.id_apply]
    split_ifs <;> simp

theorem unfoldingAffineLinearMap_apply_freeEntry (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (p : Loc.FC n' c' n c) :
    Loc.xx1 xj t (Pi.single p.1.2 1) p.1.1 = t p := by
  rw [linearMap_unfolding_apply_single, dite_eq_left p.2]

theorem map_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (s : ℕ) {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' s) : x v ∈ Loc.Ufl F n c s := by
  have key : ∀ l : Fin (n' + c'), l.1 < n' + s → x (Pi.single l 1) ∈ Loc.Ufl F n c s := by
    intro l hl
    by_cases hln : l.1 < n'
    · have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) =
          Loc.inX F n' c' (Pi.single (⟨l.1, hln⟩ : Fin n') 1) := by
        funext m
        rw [inX_apply]
        split_ifs with hm
        · by_cases hml : m = l
          · subst hml
            simp
          · have hne : (⟨m.1, hm⟩ : Fin n') ≠ ⟨l.1, hln⟩ := fun he => hml (Fin.ext (by simpa using he))
            simp [hml, hne]
        · have hml : m ≠ l := fun he => hm (he ▸ hln)
          simp [hml]
      rw [hsingle, h1]
      exact inX_mem_Ufl s _
    · have hle : n' ≤ l.1 := not_lt.1 hln
      have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) = Loc.eN F (n' + c') (n' + (l.1 - n')) := by
        funext m
        rw [Nat.add_sub_cancel' hle]
        by_cases hml : m = l
        · subst hml
          simp [Loc.eN]
        · have hv : m.1 ≠ l.1 := fun he => hml (Fin.ext he)
          simp [Loc.eN, hml, hv]
      rw [hsingle, ← sub_add_cancel (x (Loc.eN F (n' + c') (n' + (l.1 - n'))))
        (Loc.eN F (n + c) (n + (l.1 - n')))]
      exact Submodule.add_mem _ (Ufl_mono (by omega) (h3 (l.1 - n'))) (eN_mem_Ufl (by omega))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : l.1 < n' + s
  · have hsm : (Pi.single l (v l) : Fin (n' + c') → F) = v l • Pi.single l 1 := by
      funext m
      by_cases hml : m = l
      · subst hml
        simp
      · simp [hml]
    rw [hsm, map_smul]
    exact Submodule.smul_mem _ _ (key l hl)
  · have hz : v l = 0 := (mem_Ufl.1 hv) l hl
    rw [hz, Pi.single_zero, map_zero]
    exact Submodule.zero_mem _

theorem affine_action : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  intro H F _ n' c' n c hc hc' r hr r' hr' xj'
  have hR : Loc.R1cond F n c r := hr.1
  have hR' : Loc.R1cond F n' c' r' := hr'.1
  obtain ⟨γ, hγ⟩ := exists_res hr
  obtain ⟨γ', hγ'⟩ := exists_res hr'
  obtain ⟨xj, hxj⟩ : ∃ xj : (Fin n' → F) →ₗ[F] (Fin n → F),
      xj = γ.symm.toLinearMap ∘ₗ xj' ∘ₗ γ'.symm.toLinearMap := ⟨_, rfl⟩
  have hy : ∀ t, ∃ t', r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' t' := by
    intro t
    obtain ⟨c1, c2, c3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
    refine (H F n' c' n c hc hc' xj' _).2 ⟨?_, ?_, ?_⟩
    · intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hγ', c1, hγ, hxj]
      simp
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hR'.2.1, c2, hR.2.1]
    · intro s
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hsplit : r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)))) - Loc.eN F (n + c) (n + s) =
          r (Loc.xx1 xj t (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) +
            (r (Loc.eN F (n + c) (n + s)) - Loc.eN F (n + c) (n + s)) +
            r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n' + c') (n' + s))) := by
        simp only [map_sub]
        abel
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.add_mem _ (hR.1 s _ (c3 s)) (hR.2.2 s))
        (hR.1 s _ (map_Ufl c1 c3 s (hR'.2.2 s)))
  obtain ⟨f, hf⟩ : ∃ f : (Loc.FC n' c' n c → F) → (Loc.FC n' c' n c → F), ∀ t p,
      f t p = (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨_, fun _ _ => rfl⟩
  have hyf : ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (f t) := by
    intro t
    obtain ⟨t', ht'⟩ := hy t
    have hft : f t = t' := by
      funext p
      rw [hf, ht', unfoldingAffineLinearMap_apply_freeEntry]
    rw [hft, ht']
  obtain ⟨L, hL⟩ : ∃ L : (Loc.FC n' c' n c → F) →ₗ[F] (Loc.FC n' c' n c → F), ∀ t p,
      L t p = (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨{ toFun := fun t p => (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1
       map_add' := fun t u => by
         funext p
         simp only [map_add (f := _), LinearMap.add_comp, LinearMap.comp_add, LinearMap.add_apply, Pi.add_apply]
       map_smul' := fun a t => by
         funext p
         simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_apply, Pi.smul_apply,
           RingHom.id_apply] }, fun _ _ => rfl⟩
  have hxx : ∀ t : Loc.FC n' c' n c → F, Loc.xx1 xj t = linPart xj t + Loc.xx1 xj 0 := by
    intro t
    simp only [linPart, LinearMap.coe_mk, AddHom.coe_mk, sub_add_cancel]
  have hLf : ∀ t, L t + f 0 = f t := by
    intro t
    funext p
    rw [Pi.add_apply, hL, hf, hf, hxx t]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply, Pi.add_apply]
  have hinj : Function.Injective L := by
    intro t u htu
    have hfe : f t = f u := by rw [← hLf t, ← hLf u, htu]
    have hyy : r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap =
        r.toLinearMap ∘ₗ Loc.xx1 xj u ∘ₗ r'.toLinearMap := by rw [hyf t, hyf u, hfe]
    have hx : Loc.xx1 xj t = Loc.xx1 xj u := by
      refine LinearMap.ext fun v => ?_
      have hv := congrArg (fun g => r.symm (g (r'.symm v))) hyy
      simpa using hv
    funext p
    rw [← unfoldingAffineLinearMap_apply_freeEntry xj t p, ← unfoldingAffineLinearMap_apply_freeEntry xj u p, hx]
  refine ⟨xj, LinearEquiv.ofInjectiveEndo L hinj, f 0, fun t => ?_⟩
  rw [hyf t]
  congr 1
  exact (hLf t).symm

end GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpacesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  first | exact @GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | exact GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | (intros; apply GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicals
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicals
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals

variable {F : Type} [Field F] {n' c' n c : ℕ}

private theorem mem_Ufl_iff_forall_not_lt_eq_zero {N C i : ℕ} {v : Fin (N + C) → F} :
    v ∈ Loc.Ufl F N C i ↔ ∀ l : Fin (N + C), ¬ l.1 < N + i → v l = 0 := Iff.rfl

private theorem atN_add' {N : ℕ} (v w : Fin N → F) (i : ℕ) :
    Loc.atN (v + w) i = Loc.atN v i + Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

private theorem atN_smul' {N : ℕ} (a : F) (v : Fin N → F) (i : ℕ) :
    Loc.atN (a • v) i = a * Loc.atN v i := by
  unfold Loc.atN
  split_ifs <;> simp

private theorem atN_sub' {N : ℕ} (v w : Fin N → F) (i : ℕ) :
    Loc.atN (v - w) i = Loc.atN v i - Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

private theorem atN_eq_zero_of_mem_Ufl {N C i : ℕ} {v : Fin (N + C) → F} (hv : v ∈ Loc.Ufl F N C i) :
    Loc.atN v (N + i) = 0 := by
  unfold Loc.atN
  split_ifs with h
  · exact mem_Ufl_iff_forall_not_lt_eq_zero.1 hv ⟨N + i, h⟩ (lt_irrefl _)
  · rfl

private theorem atN_eN_self {N j : ℕ} (h : j < N) : Loc.atN (Loc.eN F N j) j = 1 := by
  simp [Loc.atN, Loc.eN, h]

theorem sub_atN_mem {i : ℕ} {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c (i + 1)) :
    v - Loc.atN v (n + i) • Loc.eN F (n + c) (n + i) ∈ Loc.Ufl F n c i := by
  rw [mem_Ufl_iff_forall_not_lt_eq_zero] at hv ⊢
  intro l hl
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Loc.eN]
  by_cases he : l.1 = n + i
  · rw [if_pos he]
    have hlt : n + i < n + c := by
      rw [← he]
      exact l.2
    have ha : Loc.atN v (n + i) = v l := by
      unfold Loc.atN
      rw [dite_eq_left hlt]
      congr 1
      exact Fin.ext he.symm
    rw [ha]
    ring
  · rw [if_neg he, hv l (by omega)]
    ring

private theorem Ufl_mem_succ_of_mem {N C i : ℕ} {v : Fin (N + C) → F} (hv : v ∈ Loc.Ufl F N C i) :
    v ∈ Loc.Ufl F N C (i + 1) :=
  mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => mem_Ufl_iff_forall_not_lt_eq_zero.1 hv l (fun h => hl (by omega))

private theorem eN_mem_Ufl_succ {N C i : ℕ} : Loc.eN F (N + C) (N + i) ∈ Loc.Ufl F N C (i + 1) :=
  mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => by
    simp only [Loc.eN]
    rw [if_neg]
    omega

theorem map_mem_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) (s : ℕ) :
    ∀ v ∈ Loc.Ufl F n' c' s, x v ∈ Loc.Ufl F n c s := by
  induction s with
  | zero =>
    intro v hv
    have hv' := mem_Ufl_iff_forall_not_lt_eq_zero.1 hv
    have e : v = Loc.inX F n' c' (fun j => v (Fin.castAdd c' j)) := by
      funext l
      simp only [Loc.inX, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · simp only [LinearMap.zero_apply]
        exact hv' l (by omega)
    rw [e, h1]
    apply mem_Ufl_iff_forall_not_lt_eq_zero.2
    intro l hl
    simp only [Loc.inX, LinearMap.pi_apply]
    rw [dite_eq_right (by omega)]
    rfl
  | succ s ih =>
    intro v hv
    have hd := sub_atN_mem hv
    have e : v = (v - Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s)) +
        Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s) := by abel
    rw [e, map_add (f := _), map_smul]
    refine Submodule.add_mem _ (Ufl_mem_succ_of_mem (ih _ hd)) (Submodule.smul_mem _ _ ?_)
    have e2 : x (Loc.eN F (n' + c') (n' + s)) = Loc.eN F (n + c) (n + s) +
        (x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) := by abel
    rw [e2]
    exact Submodule.add_mem _ eN_mem_Ufl_succ (Ufl_mem_succ_of_mem (h3 s))

private theorem atN_apply_eq_atN_of_mem_Ufl_succ {N' C' N C : ℕ} (y : (Fin (N' + C') → F) →ₗ[F] (Fin (N + C) → F))
    (hU : ∀ s, ∀ v ∈ Loc.Ufl F N' C' s, y v ∈ Loc.Ufl F N C s)
    (h3 : ∀ s : ℕ, y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s) ∈ Loc.Ufl F N C s)
    {s : ℕ} (hs : s < C) {v : Fin (N' + C') → F} (hv : v ∈ Loc.Ufl F N' C' (s + 1)) :
    Loc.atN (y v) (N + s) = Loc.atN v (N' + s) := by
  have hd := sub_atN_mem hv
  have hsm : Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) +
      (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) =
      y (Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) := by
    rw [map_smul]
    congr 1
    abel
  have hy : y v = y (v - Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) +
      Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) +
        (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) := by
    rw [hsm, ← map_add (f := _), sub_add_cancel]
  rw [hy, atN_add', atN_smul', atN_add', atN_eq_zero_of_mem_Ufl (hU s _ hd),
    atN_eN_self (by omega), atN_eq_zero_of_mem_Ufl (h3 s)]
  ring

theorem atN_map {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) {s : ℕ} (hs : s < c)
    {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' (s + 1)) : Loc.atN (x v) (n + s) = Loc.atN v (n' + s) := atN_apply_eq_atN_of_mem_Ufl_succ x (map_mem_Ufl h1 h3) h3 hs hv

theorem atN_eN_succ (N m : ℕ) : Loc.atN (Loc.eN F N (m + 1)) m = 0 := by
  simp [Loc.atN, Loc.eN]

private theorem atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F))
    (hU : ∀ s, ∀ v ∈ Loc.Ufl F n' c' s, x v ∈ Loc.Ufl F n c s)
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)) (hr : Loc.R1cond F n c r)
    (r' : (Fin (n' + c') → F) ≃ₗ[F] (Fin (n' + c') → F)) {i : ℕ} (hi : i < c)
    (e' : Fin (n' + c') → F) (E : Fin (n + c) → F)
    (he' : Loc.atN e' (n' + i) = 0) (hE : Loc.atN E (n + i) = 0)
    (hu' : r' e' - e' ∈ Loc.Ufl F n' c' (i + 1)) (hxe : x e' - E ∈ Loc.Ufl F n c (i + 1)) :
    Loc.atN (r (x (r' e'))) (n + i) =
      Loc.atN (x e') (n + i) + (Loc.atN (r' e') (n' + i) + Loc.atN (r E) (n + i)) := by
  have hz : x (r' e') - E ∈ Loc.Ufl F n c (i + 1) := by
    have e : x (r' e') - E = (x e' - E) + x (r' e' - e') := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ hxe (hU _ _ hu')
  have hrz : Loc.atN (r.toLinearMap (x (r' e') - E)) (n + i) = Loc.atN (x (r' e') - E) (n + i) :=
    atN_apply_eq_atN_of_mem_Ufl_succ r.toLinearMap hr.1 hr.2.2 hi hz
  have hxu : Loc.atN (x (r' e' - e')) (n + i) = Loc.atN (r' e' - e') (n' + i) :=
    atN_apply_eq_atN_of_mem_Ufl_succ x hU h3 hi hu'
  simp only [LinearEquiv.coe_coe] at hrz
  rw [map_sub, atN_sub', atN_sub', hE] at hrz
  rw [map_sub, atN_sub', atN_sub', he'] at hxu
  linear_combination hrz + hxu

theorem chArg_comp :
    (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  intro H F _ n' c' n c hc hc' r hr r' hr'
  refine ⟨∑ i ∈ Finset.range c, (Loc.atN (r' (Loc.eN F (n' + c') (n' + i + 1))) (n' + i) +
    Loc.atN (r (Loc.eN F (n + c) (n + i + 1))) (n + i)), ?_⟩
  intro xj t
  obtain ⟨hx1, -, hx3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  obtain ⟨hrc, -⟩ := hr
  obtain ⟨hr'c, -⟩ := hr'
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < c := Finset.mem_range.1 hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r _ (map_mem_Ufl hx1 hx3) hx3 r hrc r' hi' _ _ (atN_eN_succ _ _) (atN_eN_succ _ _)
    (by
      have h := hr'c.2.2 (i + 1)
      simp only [← add_assoc] at h
      exact h)
    (by
      have h := hx3 (i + 1)
      simp only [← add_assoc] at h
      exact h)

end GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicalsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  first | exact @GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | exact GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | (intros; apply GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime

theorem exists_intAt_pow_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * a) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  have h1 : P.valuation E (qOf P : E) < 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key : ∃ m : ℕ, P.valuation E ((qOf P : E) ^ m * a) ≤ 1 := by
    rcases eq_or_ne (P.valuation E a) 0 with ha | ha
    · exact ⟨0, by simp [ha]⟩
    have hq : P.valuation E (qOf P : E) ≠ 0 := by
      simpa using GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
    refine ⟨(WithZero.log (P.valuation E a)).toNat, ?_⟩
    rw [map_mul, map_pow]
    rw [← WithZero.exp_log hq, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_log hq, ← WithZero.exp_log ha, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
    set u := WithZero.log (P.valuation E (qOf P : E))
    set w := WithZero.log (P.valuation E a)
    have h2 : w ≤ (w.toNat : ℤ) := Int.self_le_toNat w
    have h3 : (0 : ℤ) ≤ (w.toNat : ℤ) := Int.natCast_nonneg _
    rw [nsmul_eq_mul]
    nlinarith
  obtain ⟨m, h⟩ := key
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer _ h
  exact ⟨m, n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem exists_intAt_family {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ i, IntAt P ((qOf P : E) ^ m' * f i) := by
  choose g hg using fun i => exists_intAt_pow_mul P (f i)
  exact ⟨Finset.univ.sup g, fun m' hm i =>
    GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono ((Finset.le_sup (Finset.mem_univ i)).trans hm) (hg i)⟩

theorem bounded_denominators : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  intro E _ _ P a b
  refine ⟨fun v => ?_, fun y => ?_⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P v
    exact ⟨m, fun m' h l => hm m' h l⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P (fun p : Fin a × Fin b => y (Pi.single p.1 1) p.2)
    exact ⟨m, fun m' h => (intHom_iff _).2 fun s l => hm m' h (s, l)⟩

end GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  first | exact @GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | exact GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | (intros; apply GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParahoricLeIntegralGl
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.parahoric_le_integral_gl

theorem inX_mem_nfLat_iff {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ)
    (e : Fin c → ℤ) (z : Sp E n) (x : Sp E n) :
    Loc.inX E n c x ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z ↔ x ∈ stdAt E n P := by
  constructor
  · rintro ⟨l, hl, s, -, h⟩
    have hs : ∀ b, s b = 0 := by
      intro b
      have h1 := congrFun h (Fin.natAdd n b)
      have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
      have h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0 := fun y => by
        rw [inX_apply, dite_eq_right (by simp)]
      have h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) =
          if b = i then ((qOf P : E) ^ e i) else 0 := by
        intro i
        unfold IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen
        rw [Pi.smul_apply, Pi.add_apply]
        have h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0 := by
          split_ifs
          · exact h2 z
          · rfl
        rw [h4]
        simp [Loc.eN, Fin.val_inj]
      rw [Pi.add_apply, h2, h2, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h
    rwa [inX_injective h]
  · intro hx
    exact ⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  rintro X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) sharp j P := by
    have := Subgroup.mem_comap.1 hr
    simpa using this
  unfold Jat at hJ
  rw [if_neg hP] at hJ
  have hk := hJ.1
  have key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P := by
    intro y
    rw [← hnf, mem_stdAt_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : h⁻¹ (h w) = w := h.symm_apply_apply w
      rw [this]
      exact (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw
    · intro hy
      exact ⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩
  rw [← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key,
    ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]
  have : (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x)) := by
    change h⁻¹ (r (h (h.symm _))) = _
    rw [h.apply_symm_apply]
  rw [this]

end GlobalTheory.Proof.parahoric_le_integral_gl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunction
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction :
    ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T']
      [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j →
      ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m']
        [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b →
        (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsQuotientMeasure j m' m ν := by
  intro T T' _ _ _ _ _ _ _ j hj m _ _ m' _ _ _ b hb hint
  refine ⟨(m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j), ?_⟩
  intro f hf
  set F : T → ℝ≥0∞ := fun t => ∫⁻ s, f (j s * t) ∂m' with hFdef
  have hF : Measurable F := by
    have hprod : Measurable fun p : T × T' => f (j p.2 * p.1) :=
      hf.comp ((hj.comp measurable_snd).mul measurable_fst)
    exact hprod.lintegral_prod_right'
  have hG : ∀ t : T,
      ∫⁻ s, f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) ∂m' = F t := by
    intro t
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel j.range) t
    obtain ⟨u, hu⟩ := QuotientGroup.rightRel_apply.mp hrel
    have ht : t = j u * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j) := by
      change t = j u * Quotient.out (Quotient.mk (QuotientGroup.rightRel j.range) t)
      rw [hu, inv_mul_cancel_right]
    simp only [hFdef]
    conv_rhs => rw [ht]
    simp_rw [← mul_assoc, ← map_mul]
    exact (lintegral_mul_right_eq_self
      (fun s => f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j))) u).symm
  set G : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j → ℝ≥0∞ := fun c => ∫⁻ s, f (j s * Quotient.out c) ∂m' with hGdef
  have hGmeas : Measurable G := by
    refine (measurable_from_quotient (s := QuotientGroup.rightRel j.range)).mpr ?_
    convert hF using 1
    funext t
    exact hG t
  have key : ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := by
    calc ∫⁻ t, f t ∂m = ∫⁻ t, (∫⁻ s, b (j s * t) ∂m') * f t ∂m :=
          lintegral_congr fun t => by rw [hint t, one_mul]
      _ = ∫⁻ t, ∫⁻ s, b (j s * t) * f t ∂m' ∂m :=
          lintegral_congr fun t => (lintegral_mul_const _ (hb.comp (hj.mul_const t))).symm
      _ = ∫⁻ s, ∫⁻ t, b (j s * t) * f t ∂m ∂m' :=
          lintegral_lintegral_swap
            ((hb.comp ((hj.comp measurable_snd).mul measurable_fst)).mul
              (hf.comp measurable_fst)).aemeasurable
      _ = ∫⁻ s, ∫⁻ t, b t * f (j s⁻¹ * t) ∂m ∂m' := lintegral_congr fun s => by
          have h := lintegral_mul_left_eq_self (μ := m) (fun t => b t * f (j s⁻¹ * t)) (j s)
          simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h
          exact h
      _ = ∫⁻ t, ∫⁻ s, b t * f (j s⁻¹ * t) ∂m' ∂m :=
          lintegral_lintegral_swap
            ((hb.comp measurable_snd).mul
              (hf.comp ((hj.comp measurable_fst.inv).mul measurable_snd))).aemeasurable
      _ = ∫⁻ t, b t * F t ∂m := lintegral_congr fun t => by
          have hmeas : Measurable fun s : T' => f (j s⁻¹ * t) :=
            hf.comp ((hj.comp measurable_inv).mul_const t)
          rw [lintegral_const_mul _ hmeas]
          congr 1
          exact lintegral_inv_eq_self (fun s => f (j s * t))
  calc ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := key
    _ = ∫⁻ t, b t * G (Quotient.mk'' t) ∂m := lintegral_congr fun t => by rw [← hG t]
    _ = ∫⁻ t, G (Quotient.mk'' t) ∂(m.withDensity b) :=
        (lintegral_withDensity_eq_lintegral_mul _ hb (hGmeas.comp measurable_quotient_mk'')).symm
    _ = ∫⁻ c, G c ∂((m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) :=
        (lintegral_map hGmeas measurable_quotient_mk'').symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunctionStatement
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isQuotientMeasure_of_bruhat : ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T'] [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j → ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m'] [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, IsQuotientMeasure j m' m ν := by
  first | exact @GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | exact GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | (intros; apply GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingBoundedIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.unfolding_bounded_integral

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n' c' n c : ℕ}

def extZ (c' c : ℕ) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F) :=
  Loc.inX F n c ∘ₗ z ∘ₗ LinearMap.funLeft F F (Fin.castAdd c')

theorem extZ_apply (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (v : Fin (n' + c') → F) :
    extZ c' c z v = Loc.inX F n c (z fun a => v (Fin.castAdd c' a)) := rfl

theorem unfoldingAffineLinearMap_add_eq_add_frM (xj z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) (t : Loc.FC n' c' n c → F) :
    Loc.xx1 (xj + a • z) t = Loc.xx1 xj t + a • extZ c' c z := by
  refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
  funext l
  change Loc.xx1 (xj + a • z) t (Pi.single s 1) l =
    Loc.xx1 xj t (Pi.single s 1) l + a * extZ c' c z (Pi.single s 1) l
  rw [linearMap_unfolding_apply_single, linearMap_unfolding_apply_single, extZ_apply, inX_apply]
  by_cases hs : s.1 < n'
  · have hf : ¬ Loc.IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
    have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) =
        Pi.single (⟨s.1, hs⟩ : Fin n') 1 := by
      funext b
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    rw [dite_eq_right hf, dite_eq_right hf, dite_eq_left hs, dite_eq_left hs, e]
    split_ifs with hl
    · simp
    · simp
  · have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) = 0 := by
      funext b
      have := b.2
      rw [Pi.single_apply, if_neg]
      · rfl
      · intro h
        apply hs
        rw [← h]
        simp
    rw [e, map_zero, dite_eq_right hs, dite_eq_right hs]
    simp

theorem chArg_add (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) :
    Loc.chArg (x + a • extZ c' c z) = Loc.chArg x := by
  unfold Loc.chArg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul, extZ_apply,
    atN_of_mem_Ufl (inX_mem_Ufl i _), mul_zero, add_zero]

end SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {v : Fin n → E} (hv : IntV P v) : IntV P (Loc.inX E n c v) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hv _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfold_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (N A B : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), HomBdd P N Psi → (∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj ≠ 0 → IntHom P (((qOf P : E) ^ N) • xj)) ∧ ∀ xj z : (Fin n' → E) →ₗ[E] (Fin n → E), IntHom P z → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi (xj + ((qOf P : E) ^ N) • z) = GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj := by
  intro E _ _ K _ P n' c' n c psi N A B Psi hPsi
  refine ⟨fun xj hx => ?_, fun xj z hz => ?_⟩
  · unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1 at hx
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    have h := hPsi.1 _ (left_ne_zero_of_mul ht)
    intro v hv a
    have h2 := h _ (intV_inX (c := c') hv) (Fin.castAdd c a)
    rw [LinearMap.smul_apply, unfoldingAffinePointMap_apply_inclusion, Pi.smul_apply, inX_castAdd] at h2
    exact h2
  · have hy : IntHom P (extZ c' c z) := fun v hv => by
      rw [extZ_apply]
      exact intV_inX (hz _ fun a => hv _)
    unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [unfoldingAffineLinearMap_add_eq_add_frM, chArg_add, hPsi.2 _ _ hy]

end GlobalTheory.Proof.unfolding_bounded_integral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormBoundsUnfolding
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.normal_form_bounds_unfolding

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance GlobalTheory.Proof.NormalFormAtPrime

variable {E : Type} [Field E] [NumberField E]

theorem nonneg_of_intAt_zpow {P : HeightOneSpectrum (𝓞 E)} {k : ℤ} (h : IntAt P ((qOf P : E) ^ k)) : 0 ≤ k := by
  by_contra hk
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
  subst hm
  obtain ⟨r, s, hs, e⟩ := h
  apply hs
  have hq := qOf_ne_zero P
  have e' : s = (qOf P : 𝓞 E) * ((qOf P : 𝓞 E) ^ m * r) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E _
    rw [map_mul, map_mul, map_pow, map_natCast, ← e, zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem le_of_zpow_eq {P : HeightOneSpectrum (𝓞 E)} {a b : ℤ} {u : E} (hu : IntAt P u)
    (h : (qOf P : E) ^ a = (qOf P : E) ^ b * u) : b ≤ a := by
  have hq := qOf_ne_zero P
  have : (qOf P : E) ^ (a - b) = u := by
    rw [zpow_sub₀ hq, h]
    field_simp
  have := nonneg_of_intAt_zpow (this ▸ hu)
  omega

variable [StarRing E] {n c : ℕ}

omit [NumberField E] [StarRing E] in
theorem inX_natAdd (x : Fin n → E) (b : Fin c) : Loc.inX E n c x (Fin.natAdd n b) = 0 := by
  rw [inX_apply, dite_eq_right (by simp)]

omit [NumberField E] [StarRing E] in
theorem atN_natAdd (v : Fin (n + c) → E) (b : Fin c) : Loc.atN v (n + b.1) = v (Fin.natAdd n b) := by
  unfold Loc.atN
  rw [dite_eq_left (by omega)]
  rfl

omit [NumberField E] [StarRing E] in
theorem nfGen_natAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i b : Fin c) :
    nfGen q n c e z i (Fin.natAdd n b) = if b = i then (q : E) ^ e i else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : (if i.1 = 0 then Loc.inX E n c z else 0 : Fin (n + c) → E) (Fin.natAdd n b) = 0 := by
    split_ifs
    · exact inX_natAdd _ _
    · rfl
  rw [h0]
  simp [Loc.eN, Fin.val_inj]

omit [NumberField E] [StarRing E] in
theorem nfGen_castAdd (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) (a : Fin n) :
    nfGen q n c e z i (Fin.castAdd c a) = if i.1 = 0 then (q : E) ^ e i * z a else 0 := by
  unfold nfGen
  rw [Pi.smul_apply, Pi.add_apply]
  have h0 : Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
    unfold Loc.eN
    rw [if_neg (by have := a.2; simp; omega)]
  rw [h0]
  split_ifs
  · rw [inX_castAdd]; simp
  · simp

theorem coords_of_mem {P : HeightOneSpectrum (𝓞 E)} (hc : 1 ≤ c) {e : Fin c → ℤ} {z : Fin n → E} {y : Fin (n + c) → E}
    (hy : y ∈ nfLat P n c e z) :
    (∀ b, ∃ u, IntAt P u ∧ y (Fin.natAdd n b) = (qOf P : E) ^ e b * u) ∧
      ∀ a, IntAt P (y (Fin.castAdd c a) - y (Fin.natAdd n ⟨0, hc⟩) * z a) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hy
  have h1 : ∀ b, (Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i : Fin (n + c) → E) (Fin.natAdd n b) =
      (qOf P : E) ^ e b * s b := by
    intro b
    rw [Pi.add_apply, inX_natAdd, Finset.sum_apply]
    simp [nfGen_natAdd, mul_comm]
  refine ⟨fun b => ⟨s b, hs b, h1 b⟩, fun a => ?_⟩
  rw [h1, Pi.add_apply, inX_castAdd, Finset.sum_apply, Finset.sum_eq_single ⟨0, hc⟩]
  · rw [Pi.smul_apply, nfGen_castAdd, if_pos rfl, smul_eq_mul]
    convert (mem_stdAt_iff l).1 hl a using 1
    ring
  · intro b _ hb
    rw [Pi.smul_apply, nfGen_castAdd, if_neg (fun h => hb (Fin.ext h)), smul_zero]
  · simp

theorem nfGen_mem (P : HeightOneSpectrum (𝓞 E)) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen (qOf P) n c e z i ∈ nfLat P n c e z :=
  ⟨0, zero_mem _, Pi.single i 1, intV_single P i, by simp [Pi.single_apply]⟩

omit [NumberField E] [StarRing E] in
theorem nfGen_mem_Ufl (q : ℕ) (e : Fin c → ℤ) (z : Fin n → E) (i : Fin c) :
    nfGen q n c e z i ∈ Loc.Ufl E n c (i.1 + 1) := by
  unfold nfGen
  refine Submodule.smul_mem _ _ (add_mem (eN_mem_Ufl (by omega)) ?_)
  split_ifs
  · exact inX_mem_Ufl _ _
  · exact zero_mem _

end GlobalTheory.Proof.normal_form_bounds_unfolding
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InfPowConjDiagUnits
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem infPow_infDiag {E : Type} [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    infPow n (infDiag k) = infPow n (diagUnits E k) := by
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E).1 = ((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).1 := by
    rw [infDiag_eq]
    rfl
  simp only [infPow, h]

end GlobalTheory.HeckeGal

end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormBilinFormsEqSumMinimiserValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSum
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.Poinc.MinSysLat

theorem finite_of_pos_lat {Y : Type} [AddCommGroup Y] {n : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ))
    (G : LinearMap.BilinForm ℤ Y) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  set G' : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    LinearMap.compl₁₂ G eb.symm.toLinearMap eb.symm.toLinearMap with hG'
  have happ : ∀ a b, G' a b = G (eb.symm a) (eb.symm b) := fun a b => rfl
  have h := GlobalTheory.Poinc.MinSys.finite_of_pos G' (fun a b => by rw [happ, happ, hs])
    (fun x => by rw [happ]; exact hn _)
    (fun x hx => by rw [happ]; exact hp _ (by simpa using hx)) B
  refine (h.preimage eb.injective.injOn).subset fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq, happ, LinearEquiv.symm_apply_apply]
  exact hx

theorem finite_minimiser_systems_lat : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  intro Y _ n N _ eb m γ hsym hnn hdef
  classical
  set G : LinearMap.BilinForm ℤ Y := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  let T : (Fin n → ZMod N) → Type := fun c =>
    {α : Y // ∀ i, ((eb α i : ℤ) : ZMod N) = c i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (γ j β.1 β.1).toNat) ≤ (fun j => (γ j α.1 α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (γ j α.1 α.1).toNat)
  choose F hF using hD
  let Bd : (Fin n → ZMod N) → ℤ := fun c => ∑ β ∈ F c, G β.1 β.1
  have hfin : {μ : (Fin n → ZMod N) → Y | ∀ c, μ c ∈ {α | G α α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => finite_of_pos_lat eb G hGsym hGnn hGpos (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, γ j β.1 β.1 ≤ γ j (μ c) (μ c) := fun j => by
    have h1 : (γ j β.1 β.1).toNat ≤ (γ j (μ c) (μ c)).toNat := hβ j
    have := hnn j β.1
    have := hnn j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * b α α = ∑ j, (cf j : ℤ) * γ j α α := fun α => by
    have := congrArg (fun f : LinearMap.BilinForm ℤ Y => f α α) hkb
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] using this
  have h2 : ∑ j, (cf j : ℤ) * γ j (μ c) (μ c) ≤ ∑ j, (cf j : ℤ) * γ j β.1 β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, γ j (μ c) (μ c) - γ j β.1 β.1 ≤
      (cf j : ℤ) * γ j (μ c) (μ c) - (cf j : ℤ) * γ j β.1 β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, γ j (μ c) (μ c) ≤ ∑ j, γ j β.1 β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : G β.1 β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => G β.1 β.1)
      (fun β _ => hGnn β.1) hβF
  rw [hGapp] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSysLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSumStatement
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat | exact GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat | (intros; apply GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesPolarizedFanLevelStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesPolarizedFanLevelStructure
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.UPoinc.CellCones

theorem cong_addHom {Y : Type} [AddCommGroup Y] {n N : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (g : Y →+ Y) {x y : Y}
    (h : ∀ i, ((eb x i : ℤ) : ZMod N) = (eb y i : ZMod N)) (i : Fin n) :
    ((eb (g x) i : ℤ) : ZMod N) = (eb (g y) i : ZMod N) := by
  have := GlobalTheory.Poinc.Cells.cong_map (eb.toLinearMap ∘ₗ g.toIntLinearMap ∘ₗ eb.symm.toLinearMap) h i
  simpa using this

theorem exists_transport {O : Type} [CommRing O] {Y : Type} [AddCommGroup Y] [Module O Y] {n N : ℕ} [NeZero N]
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y) (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (b : LinearMap.BilinForm ℤ Y) (e : Y ≃ₗ[O] Y)
    (hb : ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) :
    ∃ μ' : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i) ∧
      (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) →
        pull e.toLinearMap b (μ' cl) (μ' cl) ≤ pull e.toLinearMap b α α) ∧
      ∀ cl, ∃ d, e (μ' cl) = μ d := by
  let lift : (Fin n → ZMod N) → Y := fun cl => eb.symm fun i => ((cl i).val : ℤ)
  have hlift : ∀ cl i, ((eb (lift cl) i : ℤ) : ZMod N) = cl i := fun cl i => by simp [lift]
  let d : (Fin n → ZMod N) → (Fin n → ZMod N) := fun cl i => ((eb (e (lift cl)) i : ℤ) : ZMod N)
  refine ⟨fun cl => e.symm (μ (d cl)), fun cl i => ?_, fun cl α hα => ?_, fun cl => ⟨d cl, by simp⟩⟩
  · have h1 : ∀ i, ((eb (μ (d cl)) i : ℤ) : ZMod N) = ((eb (e (lift cl)) i : ℤ) : ZMod N) := fun i => hμ _ _
    have h2 := cong_addHom eb e.symm.toLinearMap.toAddMonoidHom h1 i
    simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
    rw [h2, hlift]
  · simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hb _ _ fun i => cong_addHom eb e.toLinearMap.toAddMonoidHom (fun i => by rw [hα, hlift]) i

theorem exists_nat_comb_of_infinite {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {b' b₀ : LinearMap.BilinForm ℤ X} (hb' : b' ∈ balForms bar X) (hb₀ : b₀ ∈ balForms bar X)
    {s : Set ℕ} (hs : s.Infinite)
    (hk : ∀ n ∈ s, ∃ (k : ℕ) (cf : Fin m → ℕ), 0 < k ∧ k • (n • b' + b₀) = ∑ j, cf j • γ j) :
    ∃ cf : Fin m → ℕ, b' = ∑ j, cf j • γ j := by
  classical
  obtain ⟨t, bb, hbb⟩ := hγ.basis
  let B' : balForms bar X := ⟨b', hb'⟩
  let B₀ : balForms bar X := ⟨b₀, hb₀⟩
  have hc : ∀ n ∈ s, ∀ o, (∀ j, o ≠ Sum.inl j) → (n : ℤ) * bb.repr B' o + bb.repr B₀ o = 0 := by
    intro n hn o ho
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x o) hE
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_nsmul, map_add (f := _), map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul] at this
    rw [Finset.sum_eq_zero fun j _ => by rw [if_neg (ho j).symm]; simp] at this
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast at this
    exact (mul_eq_zero.1 this).resolve_left hk'
  have hp : ∀ n ∈ s, ∀ j, 0 ≤ (n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j) := by
    intro n hn j
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x (Sum.inl j)) hE
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_nsmul, map_add (f := _), map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul, Sum.inl.injEq] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk0
    have h2 : (0 : ℤ) ≤ k * ((n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j)) := by
      push_cast at this ⊢; rw [this]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hk'
  let M : ℕ := ∑ o, (bb.repr B₀ o).natAbs
  obtain ⟨n₁, hn₁, h₁⟩ := hs.exists_gt M
  obtain ⟨n₂, hn₂, h₂⟩ := hs.exists_gt n₁
  have hM : ∀ o, (bb.repr B₀ o).natAbs ≤ M := fun o =>
    Finset.single_le_sum (f := fun o => (bb.repr B₀ o).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
  have hR : ∀ o, (∀ j, o ≠ Sum.inl j) → bb.repr B' o = 0 := fun o ho => by
    have e1 := hc n₁ hn₁ o ho
    have e2 := hc n₂ hn₂ o ho
    have : ((n₂ : ℤ) - n₁) * bb.repr B' o = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by omega)
  have hL : ∀ j, 0 ≤ bb.repr B' (Sum.inl j) := fun j => by
    have e1 := hp n₁ hn₁ j
    have e2 := hM (Sum.inl j)
    by_contra hneg
    push_neg at hneg
    have : (bb.repr B₀ (Sum.inl j)) ≤ M := by omega
    have : (n₁ : ℤ) * bb.repr B' (Sum.inl j) ≤ - n₁ := by nlinarith
    omega
  refine ⟨fun j => (bb.repr B' (Sum.inl j)).toNat, ?_⟩
  have hsum := bb.sum_repr B'
  have h0 : ∑ a₂ : Fin t, bb.repr B' (Sum.inr a₂) • bb (Sum.inr a₂) = 0 :=
    Finset.sum_eq_zero fun o _ => by rw [hR (Sum.inr o) fun j => Sum.inr_ne_inl, zero_smul]
  rw [Fintype.sum_sum_type, h0, add_zero] at hsum
  have := congrArg Subtype.val hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, hbb] at this
  rw [show b' = (B' : LinearMap.BilinForm ℤ X) from rfl, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← natCast_zsmul, Int.toNat_of_nonneg (hL j)]

theorem exists_finite_cones : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  intro O _ bar φ Y _ _ _ _ hF n N _ hN eb μ hμ b₀ hb₀ hb₀p hb₀m
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let Mn : ((Fin n → ZMod N) → Y) → LinearMap.BilinForm ℤ Y → Prop :=
    fun μ b => ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α
  let T : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) := {x | IsCone bar φ x.2 ∧
    (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) ∧ ∃ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin x.1 → ℕ),
      0 < k ∧ (∀ j, 0 < cf j) ∧ k • b = ∑ j, cf j • x.2 j ∧ Mn μ b}
  have hT : T.Finite := by
    obtain ⟨S, hS, hSe⟩ := hF.finite
    let TS : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) := {x | (∀ j, x.2 j ∈ S) ∧
      Function.Injective x.2 ∧ IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)}
    have hTS : TS.Finite := (GlobalTheory.Poinc.Cells.finite_families _ S hS).subset fun x hx => ⟨hx.1, hx.2.1⟩
    have hfin := fun (x : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)
      (h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)) =>
        GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb x.1 x.2 (fun j => (h.1.mem j).1) h.1.nonneg h.2
    let Fμ : (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) → Set ((Fin n → ZMod N) → Y) := fun x =>
      if h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) then ((hfin x h).choose : Set _) else ∅
    let M := (⋃ x ∈ TS, Fμ x) ∩ {μ' | ∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i}
    have hM : M.Finite := (hTS.biUnion fun x _ => by
      simp only [Fμ]; split_ifs
      · exact Finset.finite_toSet _
      · exact Set.finite_empty).inter_of_left _
    let V : Set Y := Set.range μ
    let E := ⋃ μ' ∈ M, {e : Y ≃ₗ[O] Y | ∀ cl, e (μ' cl) ∈ V}
    have hl : ∀ (e : Y ≃ₗ[O] Y) x,
        (eb.toLinearMap ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap) x = eb (e (eb.symm x)) :=
      fun e x => rfl
    have hE : E.Finite := hM.biUnion fun μ' hμ' => by
      let Φ : (Y ≃ₗ[O] Y) → (Fin n → ZMod N) → Y := fun e cl => e (μ' cl)
      refine Set.Finite.of_finite_image (f := Φ)
        ((Set.Finite.pi (t := fun _ => V) fun _ => Set.finite_range _).subset ?_) ?_
      · rintro _ ⟨e, he, rfl⟩ cl -
        exact he cl
      · intro e₁ _ e₂ _ h
        have key := GlobalTheory.Poinc.Cells.linearMap_eq_of_eq_on_residues N (by omega) n
          (eb.toLinearMap ∘ₗ e₁.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap)
          (eb.toLinearMap ∘ₗ e₂.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap)
          (Set.range fun cl => eb (μ' cl))
          (fun x => ⟨eb (μ' fun i => (x i : ZMod N)), ⟨_, rfl⟩, fun i => hμ'.2 _ _⟩) (by
            rintro _ ⟨cl, rfl⟩
            rw [hl, hl]
            simp only [LinearEquiv.symm_apply_apply]
            exact congrArg eb (congrFun h cl))
        refine LinearEquiv.ext fun y => eb.injective ?_
        have := LinearMap.congr_fun key (eb y)
        rw [hl, hl] at this
        simpa using this
    refine ((hTS.prod hE).image fun q => (⟨q.1.1, fun j => pull q.2.symm.toLinearMap (q.1.2 j)⟩ :
      Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)).subset ?_
    rintro ⟨m, γ⟩ ⟨hγ, hγd, b, k, cf, hk, hcf, hkb, hbm⟩
    obtain ⟨e, he⟩ := hSe m γ hγ
    obtain ⟨μ', hμ'1, hμ'2, hμ'3⟩ := exists_transport eb μ hμ b e hbm
    have hc' := hγ.pull_equiv e
    have hd' : ∀ y, y ≠ 0 → 0 < ∑ j, pull e.toLinearMap (γ j) y y := fun y hy => by
      simpa using hγd (e y) (by simpa using hy)
    have hkb' : k • pull e.toLinearMap b = ∑ j, cf j • pull e.toLinearMap (γ j) := LinearMap.ext₂ fun x y => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hkb (e x) (e y)
    have hx' : (⟨m, fun j => pull e.toLinearMap (γ j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ TS :=
      ⟨he, hc'.injective, hc', hd'⟩
    refine ⟨⟨⟨m, fun j => pull e.toLinearMap (γ j)⟩, e⟩, ⟨hx', ?_⟩, ?_⟩
    · refine Set.mem_biUnion (x := μ') ⟨Set.mem_biUnion hx' ?_, hμ'1⟩ fun cl => ?_
      · show μ' ∈ Fμ ⟨m, fun j => pull e.toLinearMap (γ j)⟩
        simp only [Fμ]
        rw [dite_eq_left (show IsCone bar φ (fun j => pull e.toLinearMap (γ j)) ∧ _ from ⟨hc', hd'⟩)]
        exact (hfin ⟨m, fun j => pull e.toLinearMap (γ j)⟩ ⟨hc', hd'⟩).choose_spec (pull e.toLinearMap b) k cf hk hcf
          hkb' μ' hμ'1 hμ'2
      · obtain ⟨d, hd⟩ := hμ'3 cl
        exact ⟨d, hd.symm⟩
    · simp
  obtain ⟨L, hL⟩ : ∃ L : List (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y), ∀ x, x ∈ L ↔ x ∈ T :=
    ⟨hT.toFinset.toList, fun x => by simp⟩
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, fun i => ((hL _).1 (List.get_mem L i)).1, ?_⟩
  intro b' hb' hb'p hb'm
  have key : ∀ n' : ℕ, ∃ i : Fin L.length, ∃ (k : ℕ) (cf : Fin (L.get i).1 → ℕ), 0 < k ∧
      k • (n' • b' + b₀) = ∑ j, cf j • (L.get i).2 j := by
    intro n'
    have hβs : n' • b' + b₀ ∈ balForms bar Y := add_mem (nsmul_mem hb' _) hb₀
    have hβp : ∀ x, x ≠ 0 → 0 < (n' • b' + b₀) x x := fun x hx => by
      have h1 := hb'p x
      have h2 := hb₀p x hx
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      positivity
    have hβm : Mn μ (n' • b' + b₀) := fun cl α hα => by
      have h1 := hb'm cl α hα
      have h2 := hb₀m cl α hα
      have h3 : (n' : ℤ) * b' (μ cl) (μ cl) ≤ n' * b' α α := mul_le_mul_of_nonneg_left h1 (by positivity)
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      linarith
    obtain ⟨m, γ, k, cf, hγ, hk, hcf, hkβ⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hF _ hβs hβp
    have hγd : ∀ y, y ≠ 0 → 0 < ∑ j, γ j y y := fun y hy => by
      by_contra hcon
      push_neg at hcon
      have h0 : ∀ j, γ j y y = 0 := fun j => le_antisymm ((Finset.single_le_sum (fun j _ => hγ.nonneg j y)
        (Finset.mem_univ j)).trans hcon) (hγ.nonneg j y)
      have h1 := LinearMap.congr_fun₂ hkβ y y
      have h2 := hβp y hy
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, h0, smul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h1
      have : (k : ℤ) * (n' • b' + b₀) y y > 0 := mul_pos (by exact_mod_cast hk) h2
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at this h1
      linarith
    have hmem : (⟨m, γ⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ T :=
      ⟨hγ, hγd, _, k, cf, hk, hcf, hkβ, hβm⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 ((hL _).2 hmem)
    refine ⟨i, ?_⟩
    rw [hi]
    exact ⟨k, cf, hk, hkβ⟩
  choose f hf using key
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber f
  obtain ⟨cf, hcf⟩ := exists_nat_comb_of_infinite ((hL _).1 (List.get_mem L i)).1 hb' hb₀ (s := f ⁻¹' {i})
    (Set.infinite_coe_iff.1 hi) fun n' hn' => by
      have := hf n'
      rw [show f n' = i from hn'] at this
      exact this
  exact ⟨i, 1, cf, one_pos, by rw [one_smul]; exact hcf⟩

end GlobalTheory.UPoinc.CellCones
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesPolarizedFanLevelStructureStatement
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cones_polarized_fan_level_structure : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  first | exact @GlobalTheory.UPoinc.CellCones.exists_finite_cones | exact GlobalTheory.UPoinc.CellCones.exists_finite_cones | (intros; apply GlobalTheory.UPoinc.CellCones.exists_finite_cones <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAut
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAut
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.MinSysTypeBal

theorem finite_minimiser_systems_upTo_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) →
    μ ∈ S := by
  intro O _ bar φ Y _ _ _ _ hX n N _ _ eb
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone bar φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ Y)) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ Y) x x
  let T : ι → Finset ((Fin n → ZMod N) → Y) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (h.1.mem j).1 x y)
      (fun j y => h.1.nonneg j y) h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hb hpos
  obtain ⟨m, γ, k, cf, hcone, hk, hcf, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hX b hb hpos
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j l hjl => by
    have h := congrArg Subtype.val hjl
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, (k : ℤ) * b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    have := LinearMap.congr_fun₂ hsum y y
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have h3 := hpos _ hex
    have h4 := hbyy (e x)
    simp [hz] at h4
    rcases h4 with h4 | h4
    · omega
    · omega
  have hmem : μ ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (hPi.1.mem j).1 x y)
      (fun j y => hPi.1.nonneg j y) hPi.2) (pull e.toLinearMap b) k cf hk hcf ?_ μ h1 h2
    ext a c
    have := LinearMap.congr_fun₂ hsum (e a) (e c)
    simpa [i, γ', pull_apply, LinearMap.sum_apply] using this
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysTypeBal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAutStatement
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOdd
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

theorem symm_bilin_pow_dvd_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    ∀ k : ℕ, ∀ x y, (N : ℤ) ^ k ∣ B x y := by
  have hdec : ∀ x : Y, ∃ y : Y, x = μ (fun i => (eb x i : ZMod N)) + (N : ℤ) • y := by
    intro x
    have hd : ∀ i, (N : ℤ) ∣ eb x i - eb (μ (fun i => (eb x i : ZMod N))) i := by
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hμ _ i, sub_self]
    choose z hz using hd
    refine ⟨eb.symm z, ?_⟩
    apply eb.injective
    funext i
    rw [map_add (f := _), map_smul, LinearEquiv.apply_symm_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hz i]
  have hdiag : ∀ k, (∀ x y, (N : ℤ) ^ k ∣ B x y) → ∀ x, (N : ℤ) ^ (k + 1) ∣ B x x := by
    intro k hk x
    obtain ⟨y, hy⟩ := hdec x
    have hm := h0 (fun i => (eb x i : ZMod N))
    generalize μ (fun i => (eb x i : ZMod N)) = m at hy hm
    subst hy
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hm]
    rw [hB y m]
    obtain ⟨a, ha⟩ := hk m y
    obtain ⟨b, hb⟩ := hk y y
    rw [ha, hb]
    exact ⟨2 * a + N * b, by ring⟩
  have hcop : IsCoprime (N : ℤ) 2 := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_right.mpr hodd)
    exact_mod_cast this
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    have h2 : (N : ℤ) ^ (k + 1) ∣ 2 * B x y := by
      have hxy := hdiag k ih (x + y)
      have hx := hdiag k ih x
      have hy := hdiag k ih y
      have e : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [hB y x]
        ring
      rw [e]
      exact dvd_sub (dvd_sub hxy hx) hy
    exact (hcop.pow_left).dvd_of_dvd_mul_left h2

theorem symm_bilin_eq_zero_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    B = 0 := by
  ext x y
  have h := symm_bilin_pow_dvd_of_lifts n N hodd eb μ hμ B hB h0 (B x y).natAbs x y
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem linForm_eq_sum_lifts : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  intro Y _ n N _ hN hodd eb μ hμ ℓ
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let S : Submodule ℤ (LinearMap.BilinForm ℤ Y) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ((Fin n → ZMod N) → ℤ) :=
    { toFun := fun b c => b (μ c) (μ c)
      map_add' := by intro a b; funext c; simp
      map_smul' := by intro k b; funext c; simp }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    refine symm_bilin_eq_zero_of_lifts n N hN hodd eb μ hμ _ ?_ ?_
    · intro u v
      simp [x.2 u v, y.2 u v]
    · intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp [this]
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOddStatement
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  first | exact @GlobalTheory.Poinc.linForm_eq_sum_lifts | exact GlobalTheory.Poinc.linForm_eq_sum_lifts | (intros; apply GlobalTheory.Poinc.linForm_eq_sum_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquiv
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory

theorem transport_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem transport_minimisers : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  intro O _ X Y _ _ _ _ n N _ ebX ebY f μ hμ
  let A : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebY.toLinearMap ∘ₗ f.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebX.symm.toLinearMap
  let B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebX.toLinearMap ∘ₗ f.symm.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebY.symm.toLinearMap
  have hA : ∀ x, A x = ebY (f (ebX.symm x)) := fun x => rfl
  have hB : ∀ x, B x = ebX (f.symm (ebY.symm x)) := fun x => rfl
  have hBA : ∀ x, B (A x) = x := fun x => by simp [hA, hB]
  have hAB : ∀ x, A (B x) = x := fun x => by simp [hA, hB]
  have key : ∀ (F G : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)), (∀ x, G (F x) = x) → ∀ c i,
      ((G (ebY (μ (fun i => ((F (ebY (μ c)) i : ℤ) : ZMod N)))) i : ℤ) : ZMod N) = c i := by
    intro F G hGF c i
    rw [transport_cong G _ (F (ebY (μ c))) (fun j => hμ _ j) i, hGF, hμ]
  let σ : Equiv.Perm (Fin n → ZMod N) :=
    { toFun := fun c i => ((A (ebY (μ c)) i : ℤ) : ZMod N)
      invFun := fun c i => ((B (ebY (μ c)) i : ℤ) : ZMod N)
      left_inv := fun c => by funext i; exact key A B hBA c i
      right_inv := fun c => by funext i; exact key B A hAB c i }
  refine ⟨σ, fun c i => ?_, ?_⟩
  · have := key A B hBA c i
    rw [hB, LinearEquiv.symm_apply_apply] at this
    exact this
  · intro b hmin c α hα
    simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply hmin (σ c) (f α)
    intro i
    have h1 : ebY (f α) = A (ebX α) := by rw [hA, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact transport_cong A (ebX α) (ebY (μ c)) (fun j => (hα j).trans (hμ c j).symm) i

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquivStatement
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_classMinimisers_along_linearEquiv : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  first | exact @GlobalTheory.transport_minimisers | exact GlobalTheory.transport_minimisers | (intros; apply GlobalTheory.transport_minimisers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFunEqMinIntLinearFormsOnCones
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFunEqMinIntLinearFormsOnCones
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.PolFan

theorem evalZ_eq_of_nsmul_eq_sum {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {φ : InvFun O} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ}
    (hk : 0 < k) {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) :
    φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem cones_eq_min_linear : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) →
    ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
      (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) →
      (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro O _ bar φ Y _ _ _ p m γ hγ
  have hs : ∀ i, IsStrict bar φ (γ i) := fun i => (hγ i).strict
  unfold IsStrict at hs
  choose N ℓ hN h1 h2 h3 using hs
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hb hp ⟨i, k, cf, hk, he⟩
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_nsmul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFunEqMinIntLinearFormsOnConesStatement
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invFun_eq_min_intLinearForms_on_cones : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) → ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) → (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  first | exact @GlobalTheory.PolFan.cones_eq_min_linear | exact GlobalTheory.PolFan.cones_eq_min_linear | (intros; apply GlobalTheory.PolFan.cones_eq_min_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.FinTypes

theorem single : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := GlobalTheory.T.exists_finite_cones_polarized_fan_level_structure O bar φ Y hY n N hN3 eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := GlobalTheory.T.exists_invFun_eq_min_intLinearForms_on_cones O bar φ Y p m γ hcone
  choose D ν hD hν using fun i : Fin p => GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd Y n N hN3 hNo eb μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hb' hp hm
  have hcv := hcov b' hb' hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hb' hp hcv
  have key : ∀ i, ∑ c, (((E i : ℤ) * ν i c : ℤ) : ℝ) * ((b' (μ c) (μ c) : ℤ) : ℝ)
      = ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * b' (μ c) (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hb'.1]
    push_cast at h' ⊢
    calc ∑ c, (E i : ℝ) * (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ)
        = (E i : ℝ) * ∑ c, (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) = ((E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

theorem P1 : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y), ∀ b ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms bar X, (∀ x, 0 ≤ b' x x) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo ebY
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut O bar φ Y hY n N hN3 ebY
  have hP : ∀ μ' : (Fin n → ZMod N) → Y,
      ((∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b' (μ' cl) (μ' cl) ≤ b' α α) →
        (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl)) ∧
          ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl) :=
    fun μ' ⟨h1, b₀, hb₀, h2, h3⟩ => single O bar φ Y hY n N hN3 hNo ebY μ' h1 b₀ hb₀ h2 h3
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin n → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro X _ _ _ ebX f b hb hbp μ hμ hmin
  have hbY : pull f.symm.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hbYp : ∀ x, x ≠ 0 → 0 < pull f.symm.toLinearMap b x x := fun x hx => by
    simpa using hbp (f.symm x) (by simpa using hx)
  obtain ⟨e, he⟩ := hS _ hbY hbYp
  set g : Y ≃ₗ[O] X := e.trans f.symm with hg
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.transport_classMinimisers_along_linearEquiv O Y X n N ebY ebX g μ hμ
  set μ' : (Fin n → ZMod N) → Y := fun c => g.symm (μ (σ c)) with hμ'
  have hpull : ∀ β : LinearMap.BilinForm ℤ X, pull e.toLinearMap (pull f.symm.toLinearMap β) = pull g.toLinearMap β :=
    fun β => LinearMap.ext₂ fun x y => rfl
  have hmem : μ' ∈ S := he μ' hσ1 (by rw [hpull]; exact hσ2 b hmin)
  have hgb : pull g.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hgp : ∀ x, x ≠ 0 → 0 < pull g.toLinearMap b x x := fun x hx => by
    simpa using hbp (g x) (by simpa using hx)
  have hPμ : (∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α) :=
    ⟨hσ1, _, hgb, hgp, hσ2 b hmin⟩
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  have key := hL (pull g.toLinearMap b') (pull_mem _ hb') (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull g.toLinearMap b') = φ.evalZ b' := evalZ_pull φ g.surjective b'
  have hq : ∀ c, pull g.toLinearMap b' (μ' c) (μ' c) = b' (μ (σ c)) (μ (σ c)) := fun c => by
    simp [μ']
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * b' (μ c) (μ c) =
        k * ∑ c, (ν c : ℝ) * pull g.toLinearMap b' (μ' c) (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = k * ((ιf μ' : ℝ) * φ.evalZ (pull g.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩

end GlobalTheory.UPoinc.FinTypes

theorem GlobalTheory.UPoinc.finite_types_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  intro E _ _ _ H q φ hφ N _ hN3 hNo
  classical
  obtain ⟨R, Y, hY⟩ := GlobalTheory.ProjModFinIso.finitely_many_iso_classes E q
  set B : ℕ := Module.finrank ℚ E * q + 1 with hB
  have hP : ∀ (n : ℕ) (k : Fin R), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧
      ((Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))) →
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ))
        (f : X ≃ₗ[𝓞 E] Y k), ∀ b ∈ balForms H.bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X,
        (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) →
        (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) →
        ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms H.bar X, (∀ x, 0 ≤ b' x x) →
          (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) →
          (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧
            ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) := by
    intro n k
    by_cases hC : Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))
    · obtain ⟨h1, h2, h3, ⟨ebY⟩⟩ := hC
      obtain ⟨ι, 𝓛₀, hι, h⟩ := GlobalTheory.UPoinc.FinTypes.P1 (𝓞 E) H.bar φ (Y k) (hφ (Y k) h3) n N hN3 hNo ebY
      exact ⟨ι, 𝓛₀, hι, fun _ => h⟩
    · exact ⟨1, ∅, le_rfl, fun h => (hC h).elim⟩
  choose ιf 𝓛f hιf h𝓛f using hP
  set ι : ℕ := ∏ n ∈ Finset.range B, ∏ k, ιf n k with hιdef
  have hιpos : 0 < ι := Finset.prod_pos fun n _ => Finset.prod_pos fun k _ => hιf n k
  refine ⟨B, ι, fun n => Finset.univ.biUnion fun k =>
    (𝓛f n k).image fun L => L.image fun ν c => ((ι / ιf n k : ℕ) : ℤ) * ν c, hιpos, ?_⟩
  intro n X _ _ _ _ hXq eb
  obtain ⟨hfinZ, -, hrk⟩ := GlobalTheory.finite_projective_int_of_ringOfIntegers E X
  have hn : Module.finrank ℤ X = n := by rw [eb.finrank_eq, Module.finrank_fin_fun]
  have hnB : n < B := by
    rw [hB, ← hn, hrk]
    have := Nat.mul_le_mul_left (Module.finrank ℚ E) hXq
    omega
  refine ⟨hnB, ?_⟩
  intro b hb hbp μ hμ hmin
  obtain ⟨k, ⟨f⟩⟩ := hY X hXq
  haveI h1 : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv f
  haveI h2 : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv f
  have h3 : Module.finrank (𝓞 E) (Y k) ≤ q := f.finrank_eq ▸ hXq
  have h4 : Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ)) := ⟨f.symm.toAddEquiv.toIntLinearEquiv.trans eb⟩
  obtain ⟨L, hL, hLb⟩ := h𝓛f n k ⟨h1, h2, h3, h4⟩ X eb f b hb hbp μ hμ hmin
  have hdvd : ιf n k ∣ ι := by
    have h5 : ∏ k, ιf n k ∣ ι := Finset.dvd_prod_of_mem (fun n => ∏ k, ιf n k) (Finset.mem_range.2 hnB)
    exact (Finset.dvd_prod_of_mem (fun k => ιf n k) (Finset.mem_univ k)).trans h5
  set c : ℕ := ι / ιf n k with hc
  have hcι : (ι : ℝ) = c * ιf n k := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  refine ⟨L.image fun ν cl => ((c : ℕ) : ℤ) * ν cl,
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image.2 ⟨L, hL, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLb b' hb' hb'p hb'min
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ, ∑ cl, ((((c : ℕ) : ℤ) * ν cl : ℤ) : ℝ) * b' (μ cl) (μ cl) =
      c * ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := fun ν => by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun cl _ => ?_; push_cast; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = c * ((ιf n k : ℝ) * φ.evalZ b') := by rw [hcι]; ring
  refine ⟨fun ν' hν' => ?_, ⟨_, Finset.mem_image_of_mem _ hν₀, by rw [hsum, hlhs, heq]⟩⟩
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
  rw [hsum, hlhs]
  exact mul_le_mul_of_nonneg_left (hle ν hν) hc0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.least_intCombination_minimiserCell_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  first | exact @GlobalTheory.UPoinc.finite_types_unitary | exact GlobalTheory.UPoinc.finite_types_unitary | (intros; apply GlobalTheory.UPoinc.finite_types_unitary <;> assumption)
end

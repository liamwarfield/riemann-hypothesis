module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefVFContDiffOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCuspMulStarChG
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_GL_toLin' {F : Type} [Field F] (m : ℕ) (f : Module.End F (Fin m → F) → ℂ) :
    ∑ᶠ x : GL (Fin m) F, f (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) =
      ∑ᶠ g ∈ {g : Module.End F (Fin m → F) | IsUnit g}, f g := by
  rw [← finsum_mem_univ]
  refine finsum_mem_eq_of_bijOn
    (fun x : GL (Fin m) F => (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F) : Module.End F (Fin m → F)))
    ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro x _
    exact (Units.isUnit x).map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
  · intro x _ y _ h
    exact Units.ext (Matrix.toLin'.injective h)
  · intro g hg
    have h : IsUnit ((Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).symm g) := IsUnit.map _ hg
    refine ⟨h.unit, Set.mem_univ _, ?_⟩
    exact (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).apply_symm_apply g

theorem finsum_cusp_mul_star_chG : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k l : ℕ, 0 < m → ∑ᶠ x, cusp θ m k x * star (chG (rootSum θ l) m x) = (-1) ^ (m - 1) * (Nat.card (GL (Fin m) F) : ℂ) * (((Finset.range m).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ m - 1)])).card : ℂ) := by
  intro F _ _ θ hθ m k l hm
  have hr : Module.finrank F (Fin m → F) = m := by simp
  have h := ipGL_psi_rootSum F (Fin m → F) θ hθ (by rw [hr]; exact hm) k l
  rw [hr, ipGL, ← finsum_GL_toLin', glCard] at h
  rw [mul_assoc, ← h, mul_finsum]
  refine finsum_congr fun x => ?_
  simp only [cusp, psiG, chG, Matrix.charpoly_toLin', mul_assoc]

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingCuspidalCharacterGLRootPowerSumCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingHarishChandraInductionCharpolyFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingHarishChandraInductionCharpolyFunction
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.Mass

theorem gal_id (F : Type) [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem sum_comp_surj {G M : Type} [Group G] [Group M] [Fintype G] [Fintype M]
    (π : G →* M) (hs : Function.Surjective π) (g : M → ℂ) :
    ∑ h : G, g (π h) = ((Finset.univ.filter fun h : G => π h = 1).card : ℂ) * ∑ z : M, g z := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun h => g (π h)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_congr rfl (fun h hh => by rw [(Finset.mem_filter.1 hh).2]), Finset.sum_const, nsmul_eq_mul,
    MonoidHom.card_fiber_eq_of_mem_range π (hs z) (hs 1)]

theorem aux (A B k N s : ℂ) (h : k * (A * B) ≠ 0) : A * B * ((k * (A * B))⁻¹ * (N * (k * s))) = N * s := by
  calc A * B * ((k * (A * B))⁻¹ * (N * (k * s))) = (k * (A * B)) * (k * (A * B))⁻¹ * (N * s) := by ring
    _ = N * s := by rw [mul_inv_cancel₀ h, one_mul]

theorem mass : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (S : F[X] → ℂ), (Nat.card (GL (Fin a) F) : ℂ) * (Nat.card (GL (Fin b) F) : ℂ) * ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) := by
  intro F _ _ a b n hn α β S
  obtain ⟨H, π, hH, hsurj, hπ, -, hchar⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcl : IsCl (chG S n) := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.2 S).2
  haveI : Fintype F := Fintype.ofFinite F
  set g : GL (Fin a) F × GL (Fin b) F → ℂ := fun z => α z.1 * β z.2 *
    star (S (Matrix.charpoly (z.1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (z.2 : Matrix (Fin b) (Fin b) F)))
    with hg
  have hT : ∀ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      α (tlG a (y⁻¹ * x * y)) * β (brG a b (y⁻¹ * x * y)) else 0) * star (chG S n x) = ∑ p : H, g (π p) := by
    intro y
    rw [Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _
      (fun p => (if InPar a p then α (tlG a p) * β (brG a b p) else 0) * star (chG S n p))
      (fun x => by simp [MulAut.conj_apply, show ∀ x y, chG S n (y⁻¹ * x * y) = chG S n x from hcl])]
    have h1 : ∀ p : GL (Fin n) F, (if InPar a p then α (tlG a p) * β (brG a b p) else 0) * star (chG S n p)
        = if p ∈ H then α (tlG a p) * β (brG a b p) * star (chG S n p) else 0 := by
      intro p; rw [hH p]; split_ifs <;> simp
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (p := (· ∈ H)) (by simp)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hg]
    rw [← hchar p, hπ p]
    rfl
  have hL : ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
      ∑ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      α (tlG a (y⁻¹ * x * y)) * β (brG a b (y⁻¹ * x * y)) else 0) * star (chG S n x) := by
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, Finset.sum_mul]
  have hR : ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) = ∑ z, g z := by
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
  have hP : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  have hS := sum_comp_surj π hsurj g
  have hC := sum_comp_surj π hsurj (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod] at hC
  rw [hL, hR, hP]
  simp only [hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS]
  simp only [Nat.card_eq_fintype_card]
  have hne : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hC] at hne ⊢
  push_cast at hne ⊢
  exact aux _ _ _ _ _ hne

end GlobalTheory.Shin.Mass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingHarishChandraInductionCharpolyFunctionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (S : F[X] → ℂ), (Nat.card (GL (Fin a) F) : ℂ) * (Nat.card (GL (Fin b) F) : ℂ) * ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) := by
  first | (exact @GlobalTheory.Shin.Mass.mass) | (exact GlobalTheory.Shin.Mass.mass) | (intros; apply GlobalTheory.Shin.Mass.mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingCuspidalCharacterGLRootPowerSumCharacter
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem deg_map_const_fst (m : ℕ) (e : ℕ → ℕ) (L : List ℕ) :
    deg (L.map fun i => (m, e i)) = m * L.length := by
  induction L with
  | nil => simp [deg]
  | cons a L ih =>
    simp only [deg, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem pair_prod_split {F : Type} [Field F] [Fintype F] {a b : ℕ} (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (r : ℕ → F[X] → ℂ) (hr : ∀ j, IsAdditive (r j)) (T : Finset ℕ) :
    ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y *
      star ((fun P => ∏ j ∈ T, r j P) (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) *
        Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) =
    ∑ U ∈ T.powerset, (∑ᶠ x : GL (Fin a) F, α x * star (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F)))) *
      (∑ᶠ y : GL (Fin b) F, β y * star (chG (fun P => ∏ j ∈ T \ U, r j P) b y)) := by
  simp only [finsum_eq_sum_of_fintype, chG]
  have e1 : ∀ (x : GL (Fin a) F) (y : GL (Fin b) F),
      ∏ j ∈ T, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) =
      ∑ U ∈ T.powerset, (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F))) *
        ∏ j ∈ T \ U, r j (Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) := by
    intro x y
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun j _ => hr j _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _)
  simp only [e1, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_powerset_single (i : ℕ) (S T : Finset ℕ) (hiS : i ∉ S) (hT : T.card ≤ S.card + 1)
    (f g : Finset ℕ → ℂ) (A B : ℂ) (hf0 : f ∅ = 0) (hf1 : ∀ j ∈ T, f {j} = if i = j then A else 0)
    (hg : ∀ U ∈ T.powerset, U ≠ ∅ → g U = if T \ U = S then B else 0) :
    ∑ U ∈ T.powerset, f U * g U = if T = insert i S then A * B else 0 := by
  have hz : ∀ U ∈ T.powerset, U ≠ {i} → f U * g U = 0 := by
    intro U hU hUi
    by_cases h0 : U = ∅
    · rw [h0, hf0, zero_mul]
    rw [hg U hU h0]
    split_ifs with hc
    · have hsub : U ⊆ T := Finset.mem_powerset.1 hU
      have h1 := Finset.card_sdiff_add_card_eq_card hsub
      rw [hc] at h1
      have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h0)
      have hU1 : U.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hU1
      have hjT : j ∈ T := hsub (Finset.mem_singleton_self j)
      rw [hf1 j hjT, if_neg (fun h => hUi (by rw [h])), zero_mul]
    · rw [mul_zero]
  by_cases hiT : i ∈ T
  · have hmem : {i} ∈ T.powerset := Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hiT)
    rw [Finset.sum_eq_single_of_mem {i} hmem hz, hf1 i hiT, if_pos rfl,
      hg {i} hmem (Finset.singleton_ne_empty i)]
    have hiff : (T \ {i} = S) ↔ T = insert i S := by
      constructor
      · intro h
        rw [← h, Finset.sdiff_singleton_eq_erase, Finset.insert_erase hiT]
      · intro h
        rw [h, Finset.sdiff_singleton_eq_erase, Finset.erase_insert hiS]
    by_cases hc : T = insert i S
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, mul_zero]
  · rw [Finset.sum_eq_zero fun U hU => hz U hU (fun h => hiT (by
      rw [h] at hU; exact Finset.singleton_subset_iff.1 (Finset.mem_powerset.1 hU)))]
    rw [if_neg (fun h => hiT (by rw [h]; exact Finset.mem_insert_self i S))]

theorem pair_J_prod_rootSum : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  intro F _ _ θ m e ε h1 N h2 L
  induction L with
  | nil =>
    intro T _ _ _ hT n hn
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by simpa using hT)
    subst hT0
    simp only [List.length_nil, mul_zero] at hn
    subst hn
    haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Unique (GL (Fin 0) F) := ⟨⟨1⟩, fun a => Subsingleton.elim _ _⟩
    simp [J_nil, chG, finsum_unique]
  | cons i L ih =>
    intro T hnd hLN hTN hT n hn
    haveI : Fintype F := Fintype.ofFinite F
    have hiS : i ∉ L.toFinset := by simpa using (List.nodup_cons.1 hnd).1
    have hnd' : L.Nodup := (List.nodup_cons.1 hnd).2
    have hb := deg_map_const_fst m e L
    have hn' : n = m + deg (L.map fun i => (m, e i)) := by rw [hn, hb, List.length_cons]; ring
    have hmass := GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction F m (deg (L.map fun i => (m, e i))) n hn' (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i)))) (fun P => ∏ j ∈ T, rootSum θ (e j) P)
    have hs := pair_prod_split (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))))
      (fun j => rootSum θ (e j)) (fun j => (rootSum_isAdditive_and_pow_X_sub_one F θ (e j)).1) T
    have hiN : i < N := hLN i (List.mem_cons_self ..)
    have hsum := sum_powerset_single i L.toFinset T hiS
      (by rw [List.toFinset_card_of_nodup hnd']; simpa using hT)
      (fun U => ∑ᶠ x : GL (Fin m) F, cusp θ m (e i) x *
        star (∏ j ∈ U, rootSum θ (e j) (Matrix.charpoly (x : Matrix (Fin m) (Fin m) F))))
      (fun U => ∑ᶠ y : GL (Fin (deg (L.map fun i => (m, e i)))) F,
        J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))) y *
          star (chG (fun P => ∏ j ∈ T \ U, rootSum θ (e j) P) (deg (L.map fun i => (m, e i))) y))
      ((ε : ℂ) * Nat.card (GL (Fin m) F))
      ((ε : ℂ) ^ L.length * Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F))
      (by simpa using h1 i)
      (fun j hj => by simpa [chG] using h2 i j hiN (hTN j hj))
      (fun U hU hU0 => by
        have hsub := Finset.mem_powerset.1 hU
        have hc := Finset.card_sdiff_add_card_eq_card hsub
        have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hU0)
        simp only [List.length_cons] at hT
        exact ih (T \ U) hnd' (fun k hk => hLN k (List.mem_cons_of_mem _ hk))
          (fun k hk => hTN k (Finset.mem_sdiff.1 hk).1) (by omega) _ hb)
    beta_reduce at hmass hs hsum
    rw [hs, hsum] at hmass
    have hG : ((Nat.card (GL (Fin m) F) : ℂ) *
        (Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F) : ℂ)) ≠ 0 := by
      apply mul_ne_zero <;> exact_mod_cast Nat.card_pos.ne'
    apply mul_left_cancel₀ hG
    refine hmass.trans ?_
    rw [List.toFinset_cons, List.length_cons]
    split_ifs <;> ring

end GlobalTheory.Shin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingCuspidalCharacterGLRootPowerSumCharacterStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  first | (exact @GlobalTheory.Shin.pair_J_prod_rootSum) | (exact GlobalTheory.Shin.pair_J_prod_rootSum) | (intros; apply GlobalTheory.Shin.pair_J_prod_rootSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMemEq
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

def fixSet {m : ℕ} (f : Fin m → F) : Set (GL (Fin m) F) :=
  {x | ∀ w : Fin m → F, f ⬝ᵥ w = 0 → (x : Matrix (Fin m) (Fin m) F) *ᵥ w = w}

def fixSub {m : ℕ} (f : Fin m → F) : Subgroup (GL (Fin m) F) where
  carrier := fixSet f
  one_mem' := by intro w _; simp
  mul_mem' := by
    intro x y hx hy w hw
    rw [Units.val_mul, ← mulVec_mulVec, hy w hw, hx w hw]
  inv_mem' := by
    intro x hx w hw
    calc ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w
        = ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ ((x : Matrix (Fin m) (Fin m) F) *ᵥ w) := by rw [hx w hw]
      _ = w := by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem isChar_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) (x y : G) :
    χ (y⁻¹ * x * y) = χ x := by
  obtain ⟨n, ρ, hρ⟩ := h
  rw [hρ, hρ]
  congr 1
  simpa using ρ.char_conj x y⁻¹

theorem finsum_mem_eq {α : Type} [Fintype α] (s : Set α) (g : α → ℂ) :
    ∑ᶠ x ∈ s, g x = ∑ x, if x ∈ s then g x else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp [Set.indicator_apply]

def eLast (m : ℕ) (hm : 0 < m) : Fin m → F := Pi.single (⟨m - 1, by omega⟩ : Fin m) 1

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem key {m : ℕ} (f w₀ : Fin m → F) (hw : f ⬝ᵥ w₀ = 1) (x : GL (Fin m) F) (hx : x ∈ fixSet f) :
    (x : Matrix (Fin m) (Fin m) F) = 1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f := by
  have h : ∀ w, (x : Matrix (Fin m) (Fin m) F) *ᵥ w =
      (1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f) *ᵥ w := by
    intro w
    have hw' : f ⬝ᵥ (w - (f ⬝ᵥ w) • w₀) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul, mul_one, sub_self]
    have h1 := hx _ hw'
    rw [add_mulVec, one_mulVec, vmv_mulVec, smul_sub]
    have : w = (w - (f ⬝ᵥ w) • w₀) + (f ⬝ᵥ w) • w₀ := by abel
    conv_lhs => rw [this]
    rw [mulVec_add, h1, mulVec_smul]
    abel
  ext i j
  have := congr_fun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem conj_mem {m : ℕ} (f : Fin m → F) (z x : GL (Fin m) F) :
    z⁻¹ * x * z ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ↔ x ∈ fixSet f := by
  have hzz : (z : Matrix (Fin m) (Fin m) F) * ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hzz' : ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * (z : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro h w hw
    have hw' : (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ⬝ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hzz, one_mulVec, hw]
    have := h _ hw'
    have hzw : (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = w := by
      rw [mulVec_mulVec, hzz, one_mulVec]
    simp only [Units.val_mul] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, hzw] at this
    have hzv : ∀ v, (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ v) = v := by
      intro v; rw [mulVec_mulVec, hzz, one_mulVec]
    have := congrArg (fun v => (z : Matrix (Fin m) (Fin m) F) *ᵥ v) this
    simpa only [hzv] using this
  · intro h w hw
    rw [← dotProduct_mulVec] at hw
    simp only [Units.val_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, h _ hw, mulVec_mulVec, hzz', one_mulVec]

theorem sum_conj {m : ℕ} [Fintype (GL (Fin m) F)] (f : Fin m → F) (z : GL (Fin m) F) (φ : GL (Fin m) F → ℂ) :
    (∑ x, if x ∈ fixSet f then φ (z⁻¹ * x * z) else 0) =
      ∑ g, if g ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) then φ g else 0 := by
  refine Fintype.sum_equiv (MulAut.conj z⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  rw [conj_mem]

end GlobalTheory.Shin.FreeHc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInduction
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

theorem avg {G H : Type} [Group G] [Fintype G] [Fintype H] (S : Subgroup G) (T : Set H) (hT : T.Nonempty)
    (ψ : H → G) (hψ : ∀ u ∈ T, ψ u ∈ S) (φ : G → ℂ)
    (h : ∀ g ∈ S, (∑ u, if u ∈ T then φ (g * ψ u) else 0) = 0) :
    (∑ g, if g ∈ S then φ g else 0) = 0 := by
  have h1 : ∀ u ∈ T, (∑ g, if g ∈ S then φ (g * ψ u) else 0) = ∑ g, if g ∈ S then φ g else 0 :=
    fun u hu => Fintype.sum_equiv (Equiv.mulRight (ψ u)) _ _ (fun g => by
      simp [Subgroup.mul_mem_cancel_right S (hψ u hu)])
  have h2 : (∑ u, if u ∈ T then (∑ g, if g ∈ S then φ g else 0) else 0) = 0 := by
    calc _ = ∑ u, ∑ g, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : u ∈ T
            · simp only [hu, if_true]; exact (h1 u hu).symm
            · simp [hu]
      _ = ∑ g, ∑ u, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := Finset.sum_comm
      _ = 0 := by
            refine Finset.sum_eq_zero fun g _ => ?_
            by_cases hg : g ∈ S
            · simpa [hg] using h g hg
            · simp [hg]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    obtain ⟨u, hu⟩ := hT
    have : (Finset.univ.filter (· ∈ T)).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨u, by simp [hu]⟩
    exact this (by exact_mod_cast h3)
  · exact h3

theorem sub_sum {G : Type} [Group G] [Fintype G] (H : Subgroup G) (χ : G → ℂ) :
    ∑ᶠ u : H, χ u = ∑ g, if g ∈ H then χ g else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) χ).symm

theorem hyp_eq {m : ℕ} (hm : 0 < m) :
    {x : GL (Fin m) F | ∀ i j : Fin m, (j : ℕ) + 1 < m →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j} = fixSet (eLast m hm) := by
  ext x
  simp only [Set.mem_ofPred_eq, fixSet, eLast, single_dotProduct, one_mul]
  constructor
  · intro h w hw
    ext i
    simp only [mulVec, dotProduct]
    rw [show w i = ∑ j, (1 : Matrix (Fin m) (Fin m) F) i j * w j by simp [Matrix.one_apply]]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) + 1 < m
    · rw [h i j hj]
    · have : j = ⟨m - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, hw]
      simp
  · intro h i j hj
    have hne : (⟨m - 1, by omega⟩ : Fin m) ≠ j := by
      intro h'; rw [← h'] at hj; simp at hj; omega
    have := congrFun (h (Pi.single j 1) (by rw [Pi.single_eq_of_ne hne])) i
    simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

theorem exists_row {m : ℕ} (hm : 0 < m) (f : Fin m → F) (hf : f ≠ 0) :
    ∃ z : GL (Fin m) F, eLast m hm ᵥ* (z : Matrix (Fin m) (Fin m) F) = f := by
  have he : eLast (F := F) m hm ≠ 0 := by
    intro h
    have := congrFun h ⟨m - 1, by omega⟩
    simp [eLast] at this
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) (eLast m hm) he).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) f hf))
  have h1 := hg ⟨eLast m hm, Submodule.mem_span_singleton_self _⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one F (Fin m → F) (eLast m hm) he, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  set N := LinearMap.toMatrix' g.symm.toLinearMap with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp
  have hNM : N * M = 1 := by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Mᵀ, Nᵀ, by rw [← transpose_mul, hNM, transpose_one], by rw [← transpose_mul, hMN, transpose_one]⟩, ?_⟩
  show eLast m hm ᵥ* Mᵀ = f
  rw [vecMul_transpose, hM, LinearMap.toMatrix'_mulVec]
  exact h1.symm

theorem transfer {m : ℕ} [Fintype (GL (Fin m) F)] (Y : GL (Fin m) F → ℂ) (hY : ∀ x y, Y (y⁻¹ * x * y) = Y x)
    (hfree : HFree Y) (f : Fin m → F) (hf : f ≠ 0) : (∑ x, if x ∈ fixSet f then Y x else 0) = 0 := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd (_root_.funext fun (i : Fin 0) => Fin.elim0 i) hf
    · exact h
  obtain ⟨z, hz⟩ := exists_row hm f hf
  rw [← hz, ← sum_conj (eLast m hm) z Y]
  simp only [hY]
  rw [← finsum_mem_eq, ← hyp_eq hm]
  exact hfree hm

theorem detOne {m : ℕ} (u v : Fin m → F) : (1 + vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem toG_val {m : ℕ} (u : GL (Fin m) F) : toG (u : Matrix (Fin m) (Fin m) F) = u := by
  unfold toG
  rw [dite_eq_left u.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem toG_coe {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG
  rw [dite_eq_left h]
  exact IsUnit.unit_spec _

theorem ent_castAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) (i j : Fin a) :
    ent M (i : ℕ) (j : ℕ) = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  unfold ent
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem ent_natAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) (i j : Fin b) :
    ent M (a + (i : ℕ)) (a + (j : ℕ)) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  unfold ent
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem exists_dot_one {m : ℕ} (f : Fin m → F) (hf : f ≠ 0) : ∃ w₀ : Fin m → F, f ⬝ᵥ w₀ = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
  refine ⟨Pi.single i (f i)⁻¹, ?_⟩
  rw [dotProduct_single]
  exact mul_inv_cancel₀ hi

theorem sec1 (a b : ℕ) (f : Fin (a + b) → F) (hf : (fun i => f (Fin.castAdd b i)) ≠ 0) :
    ∃ ψ : GL (Fin a) F → GL (Fin (a + b)) F, ∀ u ∈ fixSet (fun i => f (Fin.castAdd b i)),
      ψ u ∈ fixSet f ∧ InPar a (ψ u) ∧ tlG a (ψ u) = u ∧ brG a b (ψ u) = 1 := by
  set fa : Fin a → F := fun i => f (Fin.castAdd b i) with hfa
  obtain ⟨w₀, hw₀⟩ := exists_dot_one fa hf
  let vt : GL (Fin a) F → Fin (a + b) → F := fun u =>
    Fin.append ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) (0 : Fin b → F)
  refine ⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩
  have hkey := key fa w₀ hw₀ u hu
  have hdot : f ⬝ᵥ vt u = fa ⬝ᵥ ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) := by
    simp [vt, dotProduct, Fin.sum_univ_add, hfa]
  have hunit : IsUnit (1 + vecMulVec (vt u) f) := by
    rw [Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]
    exact Matrix.isUnits_det_units u
  have hc := toG_coe _ hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]
  · intro i j hj hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k := ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    have hne : Fin.natAdd a k ≠ j := fun h => by rw [← h] at hj; simp at hj
    rw [hc]
    simp [vt, vecMulVec, Matrix.one_apply, hne]
  · unfold tlG
    conv_rhs => rw [← toG_val u]
    congr 1
    ext i j
    unfold tl
    rw [ent_castAdd, hc]
    conv_rhs => rw [hkey]
    simp [vt, vecMulVec, Matrix.one_apply, hfa]
  · unfold brG
    rw [← toG_val (1 : GL (Fin b) F)]
    congr 1
    ext i j
    unfold br
    rw [ent_natAdd, hc]
    simp [vt, vecMulVec, Matrix.one_apply]

theorem sec2 (a b : ℕ) (f : Fin (a + b) → F) (h0 : (fun i => f (Fin.castAdd b i)) = 0)
    (hf : (fun j => f (Fin.natAdd a j)) ≠ 0) :
    ∃ ψ : GL (Fin b) F → GL (Fin (a + b)) F, ∀ u ∈ fixSet (fun j => f (Fin.natAdd a j)),
      ψ u ∈ fixSet f ∧ InPar a (ψ u) ∧ tlG a (ψ u) = 1 ∧ brG a b (ψ u) = u := by
  set fb : Fin b → F := fun j => f (Fin.natAdd a j) with hfb
  have h0' : ∀ i, f (Fin.castAdd b i) = 0 := fun i => congrFun h0 i
  obtain ⟨w₀, hw₀⟩ := exists_dot_one fb hf
  let vt : GL (Fin b) F → Fin (a + b) → F := fun u =>
    Fin.append (0 : Fin a → F) ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀)
  refine ⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩
  have hkey := key fb w₀ hw₀ u hu
  have hdot : f ⬝ᵥ vt u = fb ⬝ᵥ ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀) := by
    simp [vt, dotProduct, Fin.sum_univ_add, hfb]
  have hunit : IsUnit (1 + vecMulVec (vt u) f) := by
    rw [Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]
    exact Matrix.isUnits_det_units u
  have hc := toG_coe _ hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]
  · intro i j hj hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k := ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨l, rfl⟩ : ∃ l : Fin a, j = Fin.castAdd b l := ⟨⟨j, hj⟩, Fin.ext (by simp)⟩
    have hne : Fin.natAdd a k ≠ Fin.castAdd b l := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    rw [hc]
    simp [vecMulVec, Matrix.one_apply, hne, h0']
  · unfold tlG
    rw [← toG_val (1 : GL (Fin a) F)]
    congr 1
    ext i j
    unfold tl
    rw [ent_castAdd, hc]
    simp [vt, vecMulVec, Matrix.one_apply]
  · unfold brG
    conv_rhs => rw [← toG_val u]
    congr 1
    ext i j
    unfold br
    rw [ent_natAdd, hc]
    conv_rhs => rw [hkey]
    simp [vt, vecMulVec, Matrix.one_apply, hfb]

theorem coset_zero {m : ℕ} [Finite F] [Fintype (GL (Fin m) F)] (Y : GL (Fin m) F → ℂ) (hY : IsChar ℂ ℂ Y)
    (hfree : HFree Y) (f : Fin m → F) (hf : f ≠ 0) (c : GL (Fin m) F) :
    (∑ u, if u ∈ fixSet f then Y (c * u) else 0) = 0 := by
  have h0 := transfer Y (fun x y => isChar_conj hY x y) hfree f hf
  have h1 : ∑ᶠ u : fixSub f, Y u = 0 := by
    rw [sub_sum]; exact h0
  have h2 := char_coset_sum_eq_zero (GL (Fin m) F) Y hY (fixSub f) h1 c
  rw [sub_sum (fixSub f) (fun u => Y (c * u))] at h2
  exact h2

theorem core [Finite F] (a b : ℕ) [Fintype (GL (Fin (a + b)) F)] (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ)
    (hA : IsChar ℂ ℂ A) (hB : IsChar ℂ ℂ B) (hfA : HFree A) (hfB : HFree B) (f : Fin (a + b) → F) (hf : f ≠ 0) :
    (∑ g, if g ∈ fixSet f then
      (if InPar a g then A (tlG a g) * B (brG a b g) else 0) else 0) = 0 := by
  obtain ⟨P, π, hmem, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b (a + b) rfl
  have hmul : ∀ p q : GL (Fin (a + b)) F, InPar a p → InPar a q →
      InPar a (p * q) ∧ tlG a (p * q) = tlG a p * tlG a q ∧ brG a b (p * q) = brG a b p * brG a b q := by
    intro p q hp hq
    have hp' := (hmem p).2 hp
    have hq' := (hmem q).2 hq
    have h := map_mul π ⟨p, hp'⟩ ⟨q, hq'⟩
    rw [hπ, hπ, hπ] at h
    refine ⟨(hmem _).1 (P.mul_mem hp' hq'), ?_, ?_⟩
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hnot : ∀ p q : GL (Fin (a + b)) F, ¬ InPar a p → InPar a q → ¬ InPar a (p * q) := by
    intro p q hp hq hpq
    apply hp
    have := P.mul_mem ((hmem _).2 hpq) (P.inv_mem ((hmem _).2 hq))
    rw [mul_inv_cancel_right] at this
    exact (hmem _).1 this
  have hS : ∀ g, g ∈ fixSub f ↔ g ∈ fixSet f := fun _ => Iff.rfl
  simp_rw [← hS]
  by_cases h0 : (fun i => f (Fin.castAdd b i)) = 0
  · have hf2 : (fun j => f (Fin.natAdd a j)) ≠ 0 := by
      intro h2
      apply hf
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact congrFun h0 i
      · exact congrFun h2 j
    obtain ⟨ψ, hψ⟩ := sec2 a b f h0 hf2
    haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
    refine avg (fixSub f) (fixSet fun j => f (Fin.natAdd a j)) ⟨1, (fixSub _).one_mem⟩ ψ
      (fun u hu => (hψ u hu).1) _ fun g hg => ?_
    by_cases hpg : InPar a g
    · have : ∀ u, (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then
          (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) =
          A (tlG a g) * (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then B (brG a b g * u) else 0) := by
        intro u
        by_cases hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))
        · obtain ⟨-, hp, ht, hb⟩ := hψ u hu
          obtain ⟨h1, h2, h3⟩ := hmul g (ψ u) hpg hp
          simp [hu, h1, h2, h3, ht, hb]
        · simp [hu]
      rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero B hB hfB _ hf2, mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      by_cases hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))
      · simp [hu, hnot g (ψ u) hpg (hψ u hu).2.1]
      · simp [hu]
  · obtain ⟨ψ, hψ⟩ := sec1 a b f h0
    haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
    refine avg (fixSub f) (fixSet fun i => f (Fin.castAdd b i)) ⟨1, (fixSub _).one_mem⟩ ψ
      (fun u hu => (hψ u hu).1) _ fun g hg => ?_
    by_cases hpg : InPar a g
    · have : ∀ u, (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then
          (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) =
          B (brG a b g) * (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then A (tlG a g * u) else 0) := by
        intro u
        by_cases hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))
        · obtain ⟨-, hp, ht, hb⟩ := hψ u hu
          obtain ⟨h1, h2, h3⟩ := hmul g (ψ u) hpg hp
          simp [hu, h1, h2, h3, ht, hb, mul_comm]
        · simp [hu]
      rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero A hA hfA _ h0, mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      by_cases hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))
      · simp [hu, hnot g (ψ u) hpg (hψ u hu).2.1]
      · simp [hu]

theorem hfree_hc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ)
    (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  intro F _ _ a b n hn A B hA hB hfA hfB
  subst hn
  intro hpos
  haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _
  rw [hyp_eq hpos, finsum_mem_eq]
  have hgal : ∀ y : GL (Fin (a + b)) F, gal (RingHom.id F) (a + b) y = y := fun y => by
    ext; simp [gal]
  simp only [hc, hcTw, hgal, finsum_eq_sum_of_fintype]
  have : ∀ x : GL (Fin (a + b)) F, (if x ∈ fixSet (eLast (a + b) hpos) then
      (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F,
        (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) =
      (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F,
        (if x ∈ fixSet (eLast (a + b) hpos) then
          (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) := by
    intro x
    by_cases hx : x ∈ fixSet (eLast (a + b) hpos) <;> simp [hx]
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.mul_sum, Finset.sum_comm]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
  rw [sum_conj (eLast (a + b) hpos) y
    (fun g => if InPar a g then A (tlG a g) * B (brG a b g) else 0)]
  refine core a b A B hA hB hfA hfB _ ?_
  intro h
  have h2 := congrArg (fun v => v ᵥ* ((y⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)) h
  simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h2
  have h3 := congrFun h2 ⟨a + b - 1, by omega⟩
  simp [eLast] at h3

end GlobalTheory.Shin.FreeHc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInductionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.FreeHc.hfree_hc) | (exact GlobalTheory.Shin.FreeHc.hfree_hc) | (intros; apply GlobalTheory.Shin.FreeHc.hfree_hc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegree
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.PairPM

theorem rootSum_zero {K : Type} [Field K] (θ : AlgebraicClosure K →* ℂ) (P : K[X]) :
    rootSum θ 0 P = (P.natDegree : ℂ) := by
  simp only [rootSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem natCard_ext (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F' = Nat.card F ^ Module.finrank F F' := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F; haveI := Fintype.ofFinite F'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := F')]

theorem sum_cusp_eq_zero {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m e : ℕ) (hm : 0 < m)
    (h : ∀ a, ¬ e * Nat.card K ^ a ≡ 0 [MOD Nat.card K ^ m - 1]) :
    ∑ᶠ x, cusp θ m e x = 0 := by
  have H := finsum_cusp_mul_star_chG K θ hθ m e 0 hm
  have hf : (Finset.range m).filter (fun i => e * Nat.card K ^ i ≡ 0 [MOD Nat.card K ^ m - 1]) = ∅ := by
    ext i; simp [h i]
  rw [hf] at H
  have hc : ∀ x : GL (Fin m) K, star (chG (rootSum θ 0) m x) = (m : ℂ) := by
    intro x; simp [chG, rootSum_zero, Matrix.charpoly_natDegree_eq_dim]
  simp only [hc, Finset.card_empty, Nat.cast_zero, mul_zero] at H
  rw [← finsum_mul] at H
  exact (mul_eq_zero.1 H).resolve_right (by exact_mod_cast hm.ne')

theorem gram_lift {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (q l m k : ℕ) (hq : 2 ≤ q)
    (hl : 0 < l) (hm : 0 < m) (hK : Nat.card K = q ^ l) (hreg : Reg q (l * m) k) :
    ∀ i j, i < l → j < l → ∑ᶠ x, cusp θ m (k * q ^ i) x * star (chG (rootSum θ (k * q ^ j)) m x) =
      if i = j then (((-1 : ℤ) ^ (m - 1) : ℤ) : ℂ) * (Nat.card (GL (Fin m) K) : ℂ) else 0 := by
  intro i j hi hj
  rw [finsum_cusp_mul_star_chG K θ hθ m _ _ hm, hK]
  have h3 := (reg_step_of_dvd q l m k hq hl hm hreg).2.2 i j
  have hf : (Finset.range m).filter (fun a => k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1]) =
      if i = j then {0} else ∅ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha, h⟩
      obtain ⟨rfl, rfl⟩ := (h3 a hi hj ha).1 h
      simp
    · intro h
      by_cases hij : i = j
      · rw [if_pos hij, Finset.mem_singleton] at h
        subst h; subst hij
        exact ⟨hm, (h3 0 hi hi hm).2 ⟨rfl, rfl⟩⟩
      · rw [if_neg hij] at h
        simp at h
  rw [hf]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

theorem hfree_J {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
      (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1])) → HFree (J θ L (deg L))
  | [], _ => by intro h; simp [deg] at h
  | p :: L, hL => by
    have hp := hL p (List.mem_cons_self ..)
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
        (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1]) := fun p' h' => hL p' (List.mem_cons_of_mem _ h')
    rw [J_cons]
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    exact GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction K p.1 (deg L) (deg (p :: L)) hdeg _ _
      (GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular K θ hθ p.1 p.2 hp.1 hp.2.1).1
      (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular K θ hθ L (fun p' h' => ⟨(hL' p' h').1, (hL' p' h').2.1⟩) _ rfl)
      (GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField K θ hθ p.1 p.2 hp.2.2) (hfree_J θ hθ L hL')

end GlobalTheory.Shin.PairPM

namespace GlobalTheory.Shin.PairPM

theorem pairing_pm_one : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧
    ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x *
      star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  intro F F' _ _ _ _ s hl _ ι θ hθ m k n hm hn hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hK : Nat.card F' = Nat.card F ^ Module.finrank F F' := natCard_ext F F'
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  have hl0 : 0 < l := hl.pos
  have hl2 : 2 ≤ l := hl.two_le
  have hreg' : Reg q (l * m) k := hn ▸ hreg
  have hR := reg_step_of_dvd q l m k hq hl0 hm hreg'
  have hLL : liftL q l [(n, k)] = (List.range l).map (fun i => (m, k * q ^ i)) := by
    simp [liftL, hn, Nat.mul_div_cancel_left _ hl0]
  obtain ⟨hdeg, hmem⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq hl0 (by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨by rw [hn]; exact Nat.mul_pos hl0 hm, by rw [hn]; exact dvd_mul_right _ _, hreg⟩)
  have hdeg' : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hY := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftL q l [(n, k)]) (fun p hp => by rw [hK]; exact hmem p hp) n hdeg'.symm
  have hF := hfree_J θ hθ (liftL q l [(n, k)]) (by
    intro p hp
    refine ⟨(hmem p hp).1, by rw [hK]; exact (hmem p hp).2, ?_⟩
    rw [hLL, List.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases h2 : 2 ≤ m
    · exact Or.inl h2
    · right
      have h1 : m = 1 := by omega
      have := hR.2.1 (by nlinarith) i
      rw [h1, mul_one] at this
      rw [hK]
      exact this)
  rw [hdeg'] at hF
  refine ⟨((-1 : ℤ) ^ (m - 1)) ^ l, ?_, ?_⟩
  · rw [← pow_mul]
    exact neg_one_pow_eq_or ℤ _
  · rw [GlobalTheory.T.finsum_psiG_mul_star_eq_chG F' _ n _ hY hF]
    have hS : chG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n =
        chG (fun P => ∏ j ∈ Finset.range l, rootSum θ (k * q ^ j) P) n := by
      funext x
      simp only [chG]
      exact GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k _
    rw [hS]
    have hZ := GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter F' θ m (fun i => k * q ^ i) ((-1) ^ (m - 1))
      (fun i => sum_cusp_eq_zero θ hθ m _ hm (by
        intro a
        rw [hK, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        exact hR.2.1 (by nlinarith) _))
      l (gram_lift θ hθ q l m k hq hl0 hm hK hreg') (List.range l) (Finset.range l) List.nodup_range
      (fun i hi => List.mem_range.1 hi) (fun j hj => Finset.mem_range.1 hj) (by simp) n
      (by rw [hn, List.length_range, mul_comm])
    rw [List.toFinset_range, if_pos rfl, List.length_range, ← hLL] at hZ
    have hst : ∀ (a b : GL (Fin n) F' → ℂ), ∑ᶠ x, a x * star (b x) = star (∑ᶠ x, b x * star (a x)) := by
      intro a b
      rw [show star (∑ᶠ x, b x * star (a x)) = starAddEquiv (∑ᶠ x, b x * star (a x)) from rfl,
        map_finsum _ (Set.toFinite _)]
      refine finsum_congr fun x => ?_
      simp [star_mul]
    rw [hst, hZ]
    push_cast
    simp [star_pow]

end GlobalTheory.Shin.PairPM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegreeStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧ ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x * star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  first | (exact @GlobalTheory.Shin.PairPM.pairing_pm_one) | (exact GlobalTheory.Shin.PairPM.pairing_pm_one) | (intros; apply GlobalTheory.Shin.PairPM.pairing_pm_one  <;> assumption)
end

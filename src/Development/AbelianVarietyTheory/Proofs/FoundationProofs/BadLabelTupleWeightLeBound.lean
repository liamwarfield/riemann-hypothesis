module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelIdempotentLowerBoundGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsMore
namespace GlobalTheory.ComplexValueBound

open Finset

theorem main : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ), (∀ (i j : ι), i ≠ j → ∃ (k : κ), l i k ≠ l j k) → ∀ (s : Finset ι) (u : ι → M), (∀ (i : ι) (k : κ), (T k : M → M) (u i) = l i k • u i) → ∑ i ∈ s, u i = (0 : M) → ∀ i ∈ s, u i = (0 : M) := by
  intro ι κ M _ _ T l hl s
  classical
  induction s using Finset.induction_on with
  | empty => intro u _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro u hu hsum
    rw [Finset.sum_insert ha] at hsum
    have hsa : ∑ i ∈ s, u i = -u a := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hsum
    have hs : ∀ j ∈ s, u j = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      obtain ⟨k, hk⟩ := hl a j hne
      have hvu : ∀ (i : ι) (k' : κ), (T k' : M → M) ((l i k - l a k) • u i)
          = l i k' • ((l i k - l a k) • u i) := by
        intro i k'
        rw [LinearMap.map_smul, hu, smul_comm]
      have hvsum : ∑ i ∈ s, (l i k - l a k) • u i = 0 := by
        have h1 : ∑ i ∈ s, (l i k - l a k) • u i
            = T k (∑ i ∈ s, u i) - l a k • ∑ i ∈ s, u i := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hu, sub_smul]
        rw [h1, hsa, map_neg, hu, smul_neg, sub_neg_eq_add, neg_add_cancel]
      have h := ih (fun i => (l i k - l a k) • u i) hvu hvsum j hj
      exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h0 : ∑ i ∈ s, u i = 0 := Finset.sum_eq_zero hs
      rw [h0, add_zero] at hsum; exact hsum
    · exact hs i hi

end GlobalTheory.ComplexValueBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchange
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem eq_zero_of_sum_joint_eigenvectors {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ) (hl : ∀ i j, i ≠ j → ∃ k, l i k ≠ l j k)
    (s : Finset ι) : ∀ u : ι → M, (∀ i k, T k (u i) = l i k • u i) → ∑ i ∈ s, u i = 0 →
      ∀ i ∈ s, u i = 0 := by
  first
  | exact @_root_.GlobalTheory.ComplexValueBound.main
  | exact _root_.GlobalTheory.ComplexValueBound.main
  | (apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplexValueBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplexValueBound.main ..)

theorem root_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  intro G _ _ M _ _ _ ρ B X Y χ hXB hBX hc hsep n v hv hvi
  have hmul : ∀ (g h : G) (m : M), ρ (g * h) m = ρ g (ρ h m) := fun g h m => by
    rw [map_mul]; rfl
  let S : M →ₗ[ℂ] M := ∑ x : X, ρ (x : G)
  have hS : ∀ m, S m = ∑ x : X, ρ (x : G) m := fun m => by
    simp only [S, LinearMap.sum_apply]
  have hinj : ∀ m : M, (∀ b ∈ B, ρ b m = χ b • m) → (∀ y ∈ Y, ρ y m = m) → S m = 0 → m = 0 := by
    intro m hb hy h0
    rw [hS] at h0
    have := eq_zero_of_sum_joint_eigenvectors (ι := X) (κ := Y) (fun y => ρ (y : G))
      (fun x y => χ ((y : G)⁻¹ * (x : G)⁻¹ * y * x))
      (fun x x' hne => by
        obtain ⟨y, hyY, h⟩ := hsep x x.2 x' x'.2 (fun h => hne (Subtype.ext h))
        exact ⟨⟨y, hyY⟩, h⟩) Finset.univ (fun x => ρ (x : G) m)
      (fun x y => by
        have e : (y : G) * x = x * (y * ((y : G)⁻¹ * (x : G)⁻¹ * y * x)) := by group
        show ρ (y : G) (ρ (x : G) m) = _
        rw [← hmul, e, hmul, hmul, hb _ (hc x x.2 y y.2), map_smul, hy y y.2, map_smul]) h0
      1 (Finset.mem_univ _)
    simpa using this
  refine ⟨fun i => S (v i), ?_, fun i => ⟨fun b hb => ?_, fun x hx => ?_⟩⟩
  · rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg
    apply hv g
    apply hinj
    · intro b hb
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).1 b hb, smul_comm]
    · intro y hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).2 y hy]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul] using hg
  · choose f hf g hg hfg hχ using hBX b hb
    let F : X → X := fun x => ⟨f x x.2, hf x x.2⟩
    have hF : Function.Injective F := by
      intro x1 x2 h
      have h' : f x1 x1.2 = f x2 x2.2 := congrArg Subtype.val h
      have e1 := hfg x1 x1.2
      have e2 := hfg x2 x2.2
      rw [← h'] at e2
      have e : (x1 : G)⁻¹ * x2 = (g x1 x1.2)⁻¹ * g x2 x2.2 := by
        calc (x1 : G)⁻¹ * x2 = (b * x1)⁻¹ * (b * x2) := by group
          _ = _ := by rw [e1, e2]; group
      have := hXB _ (X.mul_mem (X.inv_mem x1.2) x2.2)
        (e ▸ B.mul_mem (B.inv_mem (hg x1 x1.2)) (hg x2 x2.2))
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have hB : Function.Bijective F := Finite.injective_iff_bijective.1 hF
    show ρ b (S (v i)) = χ b • S (v i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective F hB _ _ fun x => ?_
    rw [← hmul, hfg x x.2, hmul, (hvi i).1 _ (hg x x.2), hχ, map_smul]
  · show ρ x (S (v i)) = S (v i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X)) _ _ fun z => ?_
    rw [← hmul]; rfl

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchangeStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_root_subgroup_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  first | exact @GlobalTheory.BadShare.root_exchange | exact GlobalTheory.BadShare.root_exchange | (intros; apply GlobalTheory.BadShare.root_exchange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange
open Polynomial Classical GlobalTheory.BadShare

noncomputable section
namespace GlobalTheory.BadShare.RxStep

def sgOf {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) :
    Subgroup G where
  carrier := {u | S u}
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a b ha hb
  inv_mem' := fun {a} ha => by
    have hp : ∀ n : ℕ, S (a ^ n) := by
      intro n
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hm _ _ ih ha
    have ho : 0 < orderOf a := orderOf_pos a
    have : a⁻¹ = a ^ (orderOf a - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    show S a⁻¹
    rw [this]; exact hp _

theorem mem_sgOf {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v))
    (u : G) : u ∈ sgOf S h1 hm ↔ S u := Iff.rfl

theorem exists_perm {F : Type} [Field F] {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ∃ Q : GL (Fin N) F, ∀ (u : GL (Fin N) F) a b, (Q * u * Q⁻¹).val a b = u.val (σ a) (σ b) := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · intro u a b
    show (σ.toPEquiv.toMatrix * u.val * σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) a b = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp

theorem exists_cycle {N : ℕ} (i k : ℕ) (h : i + k < N) :
    ∃ σ : Equiv.Perm (Fin N), ∀ a : Fin N, (σ a : ℕ) =
      if (a : ℕ) < i then (a : ℕ) else if (a : ℕ) < i + k then a + 1 else if (a : ℕ) = i + k then i else a := by
  refine ⟨⟨fun a => ⟨if (a : ℕ) < i then (a : ℕ) else if (a : ℕ) < i + k then a + 1 else if (a : ℕ) = i + k then i else a, ?_⟩,
    fun a => ⟨if (a : ℕ) < i then (a : ℕ) else if (a : ℕ) = i then i + k else if (a : ℕ) ≤ i + k then a - 1 else a, ?_⟩,
    ?_, ?_⟩, fun a => rfl⟩
  · have := a.2; split_ifs <;> omega
  · have := a.2; split_ifs <;> omega
  · intro a; apply Fin.ext; simp only; split_ifs <;> omega
  · intro a; apply Fin.ext; simp only; split_ifs <;> omega

def tv {F : Type} [Field F] {N : ℕ} (e f : Fin N → F) (h : f ⬝ᵥ e = 0) : GL (Fin N) F :=
  ⟨1 + Matrix.vecMulVec e f, 1 - Matrix.vecMulVec e f,
    by simp [add_mul, mul_sub, Matrix.vecMulVec_mul_vecMulVec, h],
    by simp [sub_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h]⟩

theorem comm_val {F : Type} [Field F] {N : ℕ} (x y : GL (Fin N) F) (e f ξ η : Fin N → F)
    (hx : x.val = 1 + Matrix.vecMulVec e ξ) (hy : y.val = 1 + Matrix.vecMulVec η f)
    (h1 : ξ ⬝ᵥ e = 0) (h2 : f ⬝ᵥ e = 0) :
    (y⁻¹ * x⁻¹ * y * x).val = 1 + Matrix.vecMulVec e (-(ξ ⬝ᵥ η) • f) := by
  have h3 : (-(ξ ⬝ᵥ η) • f) ⬝ᵥ e = 0 := by rw [smul_dotProduct, h2, smul_zero]
  have : y⁻¹ * x⁻¹ * y * x = tv e _ h3 := by
    have : y * x = x * y * tv e _ h3 := by
      apply Units.ext
      show y.val * x.val = x.val * y.val * (1 + Matrix.vecMulVec e (-(ξ ⬝ᵥ η) • f))
      rw [hx, hy]
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.vecMulVec_mul_vecMulVec, smul_dotProduct, h1, h2,
        zero_smul, smul_zero, Matrix.vecMulVec_zero]
      simp only [neg_smul, Matrix.vecMulVec_neg]
      abel
    rw [mul_assoc, this]; group
  rw [this]; rfl

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem edge_iff (L : Lev g N) (h : L.sharp = true) (a b : Fin N) : L.Edge a b ↔
    (((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L.s ∧ ¬ (0 < L.k ∧ (a : ℕ) + 1 = L.s + L.k)) ∨
      ((a : ℕ) + 1 = L.s ∧ (b : ℕ) = L.s + L.k)) := by
  unfold Lev.Edge; rw [if_pos h]

theorem chi_eq (L : Lev g N) (h : L.sharp = true) (u : GG g N) (D : Matrix (Fin N) (Fin N) (ZMod g))
    (hu : u.val = 1 + D) (i j : Fin N) (hij : L.Edge i j) (hD : ∀ a b, L.Edge a b → a ≠ i ∨ b ≠ j → D a b = 0) :
    L.chi u = L.ψ (L.co i * D i j) := by
  have hne : ∀ a b, L.Edge a b → a ≠ b := by
    intro a b hab e
    rw [edge_iff L h, e] at hab
    omega
  unfold Lev.chi
  congr 1
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hij, hu, Matrix.add_apply, Matrix.one_apply_ne (hne _ _ hij), zero_add]
  · intro b _ hb
    split_ifs with hE
    · rw [hu, Matrix.add_apply, Matrix.one_apply_ne (hne _ _ hE), hD _ _ hE (Or.inr hb)]; simp
    · rfl
  · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with hE
    · rw [hu, Matrix.add_apply, Matrix.one_apply_ne (hne _ _ hE), hD _ _ hE (Or.inl ha)]; simp
    · rfl
  · simp

def rowGrp (i : Fin N) (W : Fin N → Prop) (hi : ¬ W i) : Subgroup (GG g N) :=
  sgOf (fun u => ∃ ξ : Fin N → ZMod g, (∀ a, ¬ W a → ξ a = 0) ∧ u.val = 1 + Matrix.vecMulVec (Pi.single i 1) ξ)
    ⟨0, fun _ _ => rfl, by simp⟩ (by
      rintro u v ⟨ξ, h, hu⟩ ⟨ξ', h', hv⟩
      refine ⟨ξ + ξ', fun a ha => by simp [h a ha, h' a ha], ?_⟩
      rw [Units.val_mul, hu, hv]
      simp [add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h i hi, Matrix.vecMulVec_add, add_assoc])

def colGrp (j : Fin N) (W : Fin N → Prop) (hj : ¬ W j) : Subgroup (GG g N) :=
  sgOf (fun u => ∃ η : Fin N → ZMod g, (∀ a, ¬ W a → η a = 0) ∧ u.val = 1 + Matrix.vecMulVec η (Pi.single j 1))
    ⟨0, fun _ _ => rfl, by simp⟩ (by
      rintro u v ⟨ξ, h, hu⟩ ⟨ξ', h', hv⟩
      refine ⟨ξ + ξ', fun a ha => by simp [h a ha, h' a ha], ?_⟩
      rw [Units.val_mul, hu, hv]
      simp [add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h' j hj, Matrix.add_vecMulVec, add_assoc])

theorem mem_of_val (L : Lev g N) (u : GG g N) (D : Matrix (Fin N) (Fin N) (ZMod g)) (hu : u.val = 1 + D)
    (h1 : ∀ a b, b ≤ a → D a b = 0)
    (h2 : ∀ a b : Fin N, L.s ≤ a → (a : ℕ) < L.s + L.k → (b : ℕ) = L.s + L.k → D a b = 0) : L.Mem u := by
  refine ⟨⟨fun a => ?_, fun a b hab => ?_⟩, fun _ a b ha hb hc => ?_⟩
  · rw [hu, Matrix.add_apply, h1 a a le_rfl]; simp
  · rw [hu, Matrix.add_apply, h1 a b hab.le, Matrix.one_apply_ne hab.ne']; simp
  · rw [hu, Matrix.add_apply, h2 a b ha hb hc, Matrix.one_apply_ne (by intro e; rw [e] at hb; omega)]; simp

theorem exchange (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M)
    (L : Lev g N) (hL : L.sharp = true) (i : Fin N) (hs : L.s = i + 1) (J' : Subgroup (GG g N))
    (hJ' : ∀ u, u ∈ J' ↔ IsUp g N u ∧ ∀ b : Fin N, L.s ≤ b → (b : ℕ) < L.s + L.k → u.val i b = 0)
    (n : ℕ) (v : Fin n → M) (hv : LinearIndependent ℂ v) (he : ∀ m, ∀ u ∈ J', ρ u (v m) = L.chi u • v m) :
    n ≤ rk ρ L.e := by
  obtain ⟨m1, mm, c1, cm, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  let j : Fin N := ⟨L.s + L.k, L.hk⟩
  have hj : (j : ℕ) = L.s + L.k := rfl
  let W : Fin N → Prop := fun a => L.s ≤ a ∧ (a : ℕ) < L.s + L.k
  have hiW : ¬ W i := by simp only [W]; omega
  have hjW : ¬ W j := by simp only [W]; omega
  have hij : L.Edge i j := by rw [edge_iff L hL]; omega
  have hji : j ≠ i := by intro e; rw [e] at hj; omega
  let J : Subgroup (GG g N) := sgOf L.Mem m1 mm
  let X : Subgroup (GG g N) := rowGrp i W hiW
  let Y : Subgroup (GG g N) := colGrp j W hjW
  have hXJ : ∀ x ∈ X, L.Mem x ∧ L.chi x = 1 := by
    rintro x ⟨ξ, h, hx⟩
    refine ⟨mem_of_val L x _ hx ?_ ?_, ?_⟩
    · intro a b hab
      rw [Matrix.vecMulVec_apply]
      by_cases ha : a = i
      · rw [h b (by simp only [W]; subst ha; have := Fin.le_def.1 hab; omega), mul_zero]
      · rw [Pi.single_eq_of_ne ha, zero_mul]
    · intro a b _ _ hb
      rw [Matrix.vecMulVec_apply, h b (by simp only [W]; omega), mul_zero]
    · rw [chi_eq L hL x _ hx i j hij, Matrix.vecMulVec_apply, h j hjW]
      · simp
      · intro a b hab _
        rw [edge_iff L hL] at hab
        rw [Matrix.vecMulVec_apply]
        by_cases ha : a = i
        · rw [h b (by simp only [W]; subst ha; omega), mul_zero]
        · rw [Pi.single_eq_of_ne ha, zero_mul]
  have hYJ : ∀ y ∈ Y, y ∈ J' ∧ L.chi y = 1 := by
    rintro y ⟨η, h, hy⟩
    have hD : ∀ a b : Fin N, b ≤ a → Matrix.vecMulVec η (Pi.single j (1 : ZMod g)) a b = 0 := by
      intro a b hab
      rw [Matrix.vecMulVec_apply]
      by_cases hb : b = j
      · rw [h a (by simp only [W]; subst hb; have := Fin.le_def.1 hab; omega), zero_mul]
      · rw [Pi.single_eq_of_ne hb, mul_zero]
    refine ⟨(hJ' y).2 ⟨⟨fun a => ?_, fun a b hab => ?_⟩, fun b hb hb' => ?_⟩, ?_⟩
    · rw [hy, Matrix.add_apply, hD a a le_rfl]; simp
    · rw [hy, Matrix.add_apply, hD a b hab.le, Matrix.one_apply_ne hab.ne']; simp
    · rw [hy, Matrix.add_apply, Matrix.vecMulVec_apply, h i hiW,
        Matrix.one_apply_ne (by intro e; rw [← e] at hb; omega)]; simp
    · rw [chi_eq L hL y _ hy i j hij, Matrix.vecMulVec_apply, h i hiW]
      · simp
      · intro a b hab _
        rw [edge_iff L hL] at hab
        rw [Matrix.vecMulVec_apply]
        by_cases hb : b = j
        · rw [h a (by simp only [W]; subst hb; omega), zero_mul]
        · rw [Pi.single_eq_of_ne hb, mul_zero]
  have hdec : ∀ u, L.Mem u → ∃ x ∈ X, u * x ∈ J ⊓ J' := by
    intro u hu
    let ξ : Fin N → ZMod g := fun a => if W a then - u.val i a else 0
    have h0 : ∀ a, ¬ W a → ξ a = 0 := fun a ha => if_neg ha
    have hd : ξ ⬝ᵥ Pi.single i 1 = 0 := by simp [h0 i hiW]
    have hx : tv (Pi.single i 1) ξ hd ∈ X := ⟨ξ, h0, rfl⟩
    have hm := mm _ _ hu (hXJ _ hx).1
    refine ⟨_, hx, hm, (hJ' _).2 ⟨hm.1, fun b hb hb' => ?_⟩⟩
    show (u.val * (1 + Matrix.vecMulVec (Pi.single i 1) ξ)) i b = 0
    have : ξ b = - u.val i b := if_pos ⟨hb, hb'⟩
    rw [mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.add_apply, Matrix.vecMulVec_apply, this]
    simp [hu.1.1 i]
  have hcomm : ∀ (x y : GG g N) (ξ η : Fin N → ZMod g), (∀ a, ¬ W a → ξ a = 0) →
      x.val = 1 + Matrix.vecMulVec (Pi.single i 1) ξ → y.val = 1 + Matrix.vecMulVec η (Pi.single j 1) →
      y⁻¹ * x⁻¹ * y * x ∈ J ⊓ J' ∧ L.chi (y⁻¹ * x⁻¹ * y * x) = L.ψ (L.co i * -(ξ ⬝ᵥ η)) := by
    intro x y ξ η h hx hy
    have hc := comm_val x y _ _ ξ η hx hy (by simp [h i hiW]) (by simp [Pi.single_eq_of_ne hji.symm])
    have hD : ∀ a b : Fin N, a ≠ i ∨ b ≠ j →
        Matrix.vecMulVec (Pi.single i (1 : ZMod g)) (-(ξ ⬝ᵥ η) • Pi.single j (1 : ZMod g)) a b = 0 := by
      rintro a b (ha | hb)
      · rw [Matrix.vecMulVec_apply, Pi.single_eq_of_ne ha, zero_mul]
      · rw [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.single_eq_of_ne hb, smul_zero, mul_zero]
    have hm : L.Mem (y⁻¹ * x⁻¹ * y * x) := by
      refine mem_of_val L _ _ hc (fun a b hab => hD a b ?_) (fun a b ha _ _ => hD a b (Or.inl ?_))
      · by_contra hcon
        push_neg at hcon
        rw [hcon.1, hcon.2, Fin.le_def] at hab
        omega
      · intro e; rw [e] at ha; omega
    refine ⟨⟨hm, (hJ' _).2 ⟨hm.1, fun b hb hb' => ?_⟩⟩, ?_⟩
    · rw [hc, Matrix.add_apply, hD i b (Or.inr (by intro e; rw [e] at hb'; omega)),
        Matrix.one_apply_ne (by intro e; rw [← e] at hb; omega)]; simp
    · rw [chi_eq L hL _ _ hc i j hij (fun a b _ h => hD a b h), Matrix.vecMulVec_apply]
      simp
  obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.representation_root_subgroup_exchange (GG g N) M ρ (J ⊓ J') X Y L.chi
    (by
      rintro x ⟨ξ, h, hx⟩ hB
      have : ξ = 0 := by
        funext b
        by_cases hb : W b
        · have := ((hJ' x).1 hB.2).2 b hb.1 hb.2
          rw [hx, Matrix.add_apply, Matrix.one_apply_ne (by intro e; rw [← e] at hb; exact hiW hb),
            Matrix.vecMulVec_apply] at this
          simpa using this
        · exact h b hb
      apply Units.ext
      rw [hx, this]; simp)
    (by
      intro b hb x hx
      have hbx : b * x ∈ J := J.mul_mem hb.1 (hXJ x hx).1
      obtain ⟨x', hx', hb'⟩ := hdec _ (J.inv_mem hbx)
      refine ⟨x', hx', ((b * x)⁻¹ * x')⁻¹, Subgroup.inv_mem _ hb', by group, ?_⟩
      have e : x' * ((b * x)⁻¹ * x')⁻¹ = b * x := by group
      have h1 := cm _ _ (hXJ x' hx').1 (J.inv_mem hb'.1)
      rw [e, cm _ _ hb.1 (hXJ x hx).1, (hXJ x hx).2, (hXJ x' hx').2] at h1
      simpa using h1.symm)
    (by
      rintro x ⟨ξ, h, hx⟩ y ⟨η, _, hy⟩
      exact (hcomm x y ξ η h hx hy).1)
    (by
      rintro x ⟨ξ, h, hx⟩ x' ⟨ξ', h', hx'⟩ hne
      have hξ : ξ ≠ ξ' := by
        intro e; apply hne; apply Units.ext; rw [hx, hx', e]
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hξ
      have haW : W a := by
        by_contra hc; exact ha (by rw [h a hc, h' a hc])
      obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 L.hψ
      have hc : (L.co i : ZMod g) * (ξ' a - ξ a) ≠ 0 := mul_ne_zero (L.co i).ne_zero (sub_ne_zero.2 ha.symm)
      let η : Fin N → ZMod g := Pi.single a (t / ((L.co i : ZMod g) * (ξ' a - ξ a)))
      have h0 : ∀ b, ¬ W b → η b = 0 := fun b hb => Pi.single_eq_of_ne (by intro e; rw [e] at hb; exact hb haW) _
      have hd : (Pi.single j 1 : Fin N → ZMod g) ⬝ᵥ η = 0 := by simp [h0 j hjW]
      refine ⟨tv η (Pi.single j 1) hd, ⟨η, h0, rfl⟩, ?_⟩
      rw [(hcomm x _ ξ η h hx rfl).2, (hcomm x' _ ξ' η h' hx' rfl).2]
      intro e
      apply ht
      have e2 : (L.co i : ZMod g) * -(ξ ⬝ᵥ η) = t + L.co i * -(ξ' ⬝ᵥ η) := by
        simp only [η, dotProduct_single]
        have h3 := left_ne_zero_of_mul hc
        have h4 := right_ne_zero_of_mul hc
        field_simp
        ring
      rw [e2, AddChar.map_add_eq_mul] at e
      have hn : L.ψ (L.co i * -(ξ' ⬝ᵥ η)) ≠ 0 := by
        intro h5
        have := L.ψ.map_add_eq_mul (L.co i * -(ξ' ⬝ᵥ η)) (-(L.co i * -(ξ' ⬝ᵥ η)))
        rw [h5] at this
        simp at this
      exact mul_right_cancel₀ hn (by rw [e, one_mul]))
    n v hv
    (fun m => ⟨fun b hb => he m b hb.2, fun y hy => by rw [he m y (hYJ y hy).1, (hYJ y hy).2, one_smul]⟩)
  refine (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L.Mem L.chi m1 mm c1 cm).2.2.2 n w hw ?_
  intro m u hu
  obtain ⟨x, hx, hb⟩ := hdec u hu
  have e : u = (u * x) * x⁻¹ := by group
  have h1 := cm _ _ hu (hXJ x hx).1
  rw [(hXJ x hx).2, mul_one] at h1
  calc ρ u (w m) = ρ (u * x) (ρ x⁻¹ (w m)) := by rw [← Module.End.mul_apply, ← map_mul, ← e]
    _ = _ := by rw [(hw' m).2 _ (X.inv_mem hx), (hw' m).1 _ hb, h1]

theorem rk_le_step : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = true → L'.sharp = true → L.k = L'.k → L.s = L'.s + 1 → rk ρ L'.e ≤ rk ρ L.e := by
  intro g _ N M _ _ _ ρ L L' hL hL' hk hs
  have hN := L.hk
  obtain ⟨σ, hσ⟩ := exists_cycle (N := N) L'.s L'.k L'.hk
  obtain ⟨Q, hQ⟩ := exists_perm (F := ZMod g) σ
  let K : Lev g N := ⟨true, L'.s, L'.k, L'.hk, L.ψ, L.hψ, fun a => L.co (σ a)⟩
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L' K hL' rfl rfl]
  obtain ⟨m1, mm, c1, cm, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N K
  have hE : ∀ a b, K.Edge a b ↔ L.Edge (σ a) (σ b) := by
    intro a b
    rw [edge_iff K rfl, edge_iff L hL, hσ, hσ, hk, hs]
    show (((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L'.s ∧ ¬ (0 < L'.k ∧ (a : ℕ) + 1 = L'.s + L'.k)) ∨
      ((a : ℕ) + 1 = L'.s ∧ (b : ℕ) = L'.s + L'.k)) ↔ _
    split_ifs <;> omega
  have hchi : ∀ u, K.chi (Q * u * Q⁻¹) = L.chi u := by
    intro u
    unfold Lev.chi
    show L.ψ _ = L.ψ _
    congr 1
    refine Fintype.sum_equiv σ _ _ fun a => ?_
    refine Fintype.sum_equiv σ _ _ fun b => ?_
    rw [hQ]
    exact if_congr (hE a b) rfl rfl
  let i : Fin N := ⟨L'.s, by omega⟩
  have hi : (i : ℕ) = L'.s := rfl
  let J' : Subgroup (GG g N) := sgOf (fun u => K.Mem (Q * u * Q⁻¹)) (by simpa using m1) (by
    intro u v hu hv
    have : Q * (u * v) * Q⁻¹ = (Q * u * Q⁻¹) * (Q * v * Q⁻¹) := by group
    rw [this]; exact mm _ _ hu hv)
  have hJ' : ∀ u, u ∈ J' ↔ IsUp g N u ∧ ∀ b : Fin N, L.s ≤ b → (b : ℕ) < L.s + L.k → u.val i b = 0 := by
    intro u
    rw [mem_sgOf]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [hQ] at h1 h2 h3
      have h4 : ∀ a b : Fin N, L'.s ≤ a → (a : ℕ) < L'.s + L'.k → (b : ℕ) = L'.s + L'.k → u.val (σ a) (σ b) = 0 :=
        h3 rfl
      refine ⟨⟨fun a => by simpa using h1 (σ.symm a), fun a b hab => ?_⟩, fun b hb hb' => ?_⟩
      · obtain ⟨a, rfl⟩ := σ.surjective a
        obtain ⟨b, rfl⟩ := σ.surjective b
        by_cases hc : b < a
        · exact h2 a b hc
        · rw [Fin.lt_def, hσ, hσ] at hab
          rw [Fin.lt_def] at hc
          apply h4 <;> split_ifs at hab <;> omega
      · obtain ⟨a, ha⟩ := σ.surjective i
        obtain ⟨b, rfl⟩ := σ.surjective b
        rw [← ha]
        apply h2
        have h5 := congrArg Fin.val ha
        rw [hσ] at h5 hb hb'
        rw [Fin.lt_def]
        split_ifs at h5 hb hb' <;> omega
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨fun a => by rw [hQ]; exact h1 _, fun a b hab => ?_⟩, fun _ a b ha ha' hb => ?_⟩
      · rw [hQ]
        by_cases hc : σ b < σ a
        · exact h2 _ _ hc
        · rw [Fin.lt_def, hσ, hσ] at hc
          rw [Fin.lt_def] at hab
          have : σ a = i := by
            apply Fin.ext; rw [hσ, hi]; split_ifs at hc ⊢ <;> omega
          rw [this]
          apply h3 <;> rw [hσ] <;> split_ifs at hc ⊢ <;> omega
      · rw [hQ]
        apply h2
        change L'.s ≤ a at ha
        change (a : ℕ) < L'.s + L'.k at ha'
        change (b : ℕ) = L'.s + L'.k at hb
        rw [Fin.lt_def, hσ, hσ]
        split_ifs <;> omega
  have hr := (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ K.Mem K.chi m1 mm c1 cm).2.2.1
  let bs := Module.finBasis ℂ (LinearMap.range (op ρ K.e))
  have hinj : LinearMap.ker (ρ Q⁻¹ ∘ₗ (LinearMap.range (op ρ K.e)).subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have := congrArg (ρ Q) hxy
    apply Subtype.ext
    simpa [← Module.End.mul_apply, ← map_mul] using this
  refine exchange M ρ L hL i hs J' hJ' _ _ (bs.linearIndependent.map' _ hinj) ?_
  intro m u hu
  show ρ u (ρ Q⁻¹ (bs m).1) = L.chi u • ρ Q⁻¹ (bs m).1
  have h1 := (hr (bs m).1).1 (bs m).2 _ hu
  rw [← map_smul, ← hchi, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

end GlobalTheory.BadShare.RxStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchangeStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = true → L'.sharp = true → L.k = L'.k → L.s = L'.s + 1 → rk ρ L'.e ≤ rk ρ L.e := by
  first | exact @GlobalTheory.BadShare.RxStep.rk_le_step | exact GlobalTheory.BadShare.RxStep.rk_le_step | (intros; apply GlobalTheory.BadShare.RxStep.rk_le_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelIdempotentLowerBoundGeneric
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem one_le_rk_of_not_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (L : Lev g N)
    (hL : L.sharp = false) : 1 ≤ rk ρ L.e := by
  obtain ⟨L₀, h₀, x, hx, hu⟩ := hρ
  let L' : Lev g N := { L₀ with s := L.s, k := L.k, hk := L.hk }
  have hs : L'.sharp = false := h₀
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L' (hL.trans hs.symm) rfl rfl]
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L'
  obtain ⟨-, -, -, h⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L'.Mem L'.chi a1 a2 a3 a4
  refine h 1 (fun _ => x) (linearIndependent_unique_iff.2 hx) ?_
  intro i u hm
  have hchi : L'.chi u = L₀.chi u := by
    simp only [Lev.chi, Lev.Edge, hs, h₀, Bool.false_eq_true, if_false]
    rfl
  rw [hchi]
  exact hu u hm.1

theorem rk_lower_of_sharp (g : ℕ) [Fact g.Prime] (N : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M) (hρ : IsGeneric ρ) (s : ℕ) :
    ∀ L : Lev g N, L.sharp = true → L.s = s → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  induction s with
  | zero => exact fun L h1 h2 => GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first g N M ρ hρ L h1 h2
  | succ s ih =>
    intro L h1 h2
    have hk : s + L.k < N := by have := L.hk; omega
    let L' : Lev g N := { L with s := s, hk := hk }
    have h3 := ih L' h1 rfl
    have h4 := GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange g N M ρ L L' h1 h1 rfl h2
    exact h3.trans (by exact_mod_cast h4)

theorem rk_lev_lower : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  intro g _ N M _ _ _ ρ hρ L
  by_cases h : L.sharp = true
  · rw [if_pos h]
    exact rk_lower_of_sharp g N M ρ hρ L.s L h rfl
  · rw [if_neg h, pow_zero, mul_one]
    have h1 : (1 : ℝ) ≤ rk ρ L.e := by
      exact_mod_cast one_le_rk_of_not_sharp g N M ρ hρ L (by simpa using h)
    have h2 : (0 : ℝ) ≤ 1 / (g : ℝ) := by positivity
    linarith

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelIdempotentLowerBoundGenericStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_levelIdempotent_lower_bound_generic : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  first | exact @GlobalTheory.BadShare.rk_lev_lower | exact GlobalTheory.BadShare.rk_lev_lower | (intros; apply GlobalTheory.BadShare.rk_lev_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPow
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

def levMat {g N : ℕ} (S : Finset (Fin N × Fin N)) (f : S → ZMod g) : Matrix (Fin N) (Fin N) (ZMod g) :=
  fun a b => if h : (a, b) ∈ S then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem levMat_det {g N : ℕ} (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) (f : S → ZMod g) :
    (levMat S f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro a _
    have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
    simp [levMat, this]
  · intro a b hab
    have hab' : b < a := hab
    have : (a, b) ∉ S := fun h => lt_asymm hab' (hS _ h)
    simp [levMat, this, hab'.ne']

theorem card_up_supp (g : ℕ) [Fact g.Prime] (N : ℕ) (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} = g ^ S.card := by
  have e : {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} ≃ (S → ZMod g) :=
    { toFun := fun u p => u.1.val p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (levMat S f) (by rw [levMat_det S hS]; exact one_ne_zero), by
        refine ⟨fun a => ?_, fun a b hab h => ?_⟩
        · have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
          show levMat S f a a = 1
          simp [levMat, this]
        · show levMat S f a b = 0
          simp [levMat, h, hab]⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        ext a b
        show levMat S (fun p => u.1.val p.1.1 p.1.2) a b = u.1.val a b
        unfold levMat
        split_ifs with h1 h2
        · rfl
        · subst h2; exact (u.2.1 a).symm
        · exact (u.2.2 a b h2 h1).symm
      right_inv := fun f => by
        funext p
        show levMat S f p.1.1 p.1.2 = f p
        simp [levMat, p.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  simp

theorem lev_card : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N,
    Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  intro g _ N L
  set U : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2) with hU
  set R : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => L.sharp = true ∧ L.s ≤ p.1 ∧ (p.1 : ℕ) < L.s + L.k ∧ (p.2 : ℕ) = L.s + L.k) with hR
  have hUc : U.card = N * (N - 1) / 2 := by
    rw [hU, Finset.card_product_filter_lt, Nat.choose_two_right]
    simp
  have hRU : R ⊆ U := by
    intro p hp
    simp only [hR, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
    rw [Fin.lt_def]
    omega
  have hRc : R.card = if L.sharp = true then L.k else 0 := by
    split_ifs with h
    · have hk := L.hk
      symm
      rw [← Finset.card_range L.k]
      refine Finset.card_bij (fun i hi => (⟨L.s + i, by have := Finset.mem_range.1 hi; omega⟩, ⟨L.s + L.k, hk⟩)) ?_ ?_ ?_
      · intro i hi
        have := Finset.mem_range.1 hi
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact ⟨by omega, by omega, trivial⟩
      · intro i hi j hj hij
        have := congrArg (fun p : Fin N × Fin N => (p.1 : ℕ)) hij
        simp only at this
        omega
      · intro p hp
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h] at hp
        refine ⟨p.1 - L.s, Finset.mem_range.2 (by omega), ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    · simp [hR, h]
  have hM : ∀ u : GG g N, L.Mem u ↔
      ((∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ U \ R → u.val a b = 0) := by
    intro u
    simp only [Lev.Mem, IsUp, hU, hR, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, not_and, not_not]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun a b hab h => ?_⟩
      rcases lt_or_gt_of_ne hab with h' | h'
      · by_contra hne
        exact h h' (fun x1 x2 x3 x4 => hne (h3 x1 a b x2 x3 x4))
      · exact h2 a b h'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun a b h => h2 a b h.ne' (fun h' => absurd h' (lt_asymm h))⟩, fun x1 a b x2 x3 x4 => ?_⟩
      refine h2 a b (fun h => ?_) (fun _ h => h x1 x2 x3 x4)
      subst h
      omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight hM), card_up_supp g N (U \ R) (fun p hp => by
    have := (Finset.mem_sdiff.1 hp).1
    exact (Finset.mem_filter.1 this).2), ← hRc, ← pow_add, Finset.card_sdiff_add_card_eq_card hRU, hUc]

end GlobalTheory.BadShare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPowStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_levelDatum_group_mul_pow : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  first | exact @GlobalTheory.BadShare.lev_card | exact GlobalTheory.BadShare.lev_card | (intros; apply GlobalTheory.BadShare.lev_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeField
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeField
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem prod_pow_sub_pow_eq (g N : ℕ) :
    ∏ i ∈ Finset.range N, (g ^ N - g ^ i)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  have h1 : ∀ i ∈ Finset.range N, g ^ N - g ^ i = g ^ i * (g ^ (N - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Finset.prod_range_reflect (fun i => g ^ (i + 1) - 1) N]

theorem card_GG_eq (g : ℕ) [Fact g.Prime] (N : ℕ) :
    Fintype.card (GG g N)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  rw [← prod_pow_sub_pow_eq, ← Nat.card_eq_fintype_card]
  have h := Matrix.card_GL_field (𝔽 := ZMod g) N
  rw [ZMod.card] at h
  rw [← Fin.prod_univ_eq_prod_range (fun i => g ^ N - g ^ i) N]
  exact h

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGeneralLinearGroupPrimeFieldStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_generalLinearGroup_primeField : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), Fintype.card (GG g N) = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  first | exact @GlobalTheory.BadShare.card_GG_eq | exact GlobalTheory.BadShare.card_GG_eq | (intros; apply GlobalTheory.BadShare.card_GG_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBound
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem series_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  intro g hg N L τ hτ f hf
  obtain ⟨V, hV, hchar, hgen, hdim⟩ := hτ.2 f hf
  obtain ⟨h1, hmul, hc1, hcmul, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  obtain ⟨hproj, he1, -, -⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) V V.ρ L.Mem L.chi h1 hmul hc1 hcmul
  have hz := (GlobalTheory.T.centralIdempotent_irreducible_character_props (GG g N) V).2.2.2 L.e hproj.1
  have hT : 0 < torusCard g f := ((GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf).1
  have hr := GlobalTheory.T.rank_levelIdempotent_lower_bound_generic g N V V.ρ hgen L
  have hJ := GlobalTheory.T.card_levelDatum_group_mul_pow g N L
  have hG := GlobalTheory.T.card_generalLinearGroup_primeField g N
  have hGpos : 0 < Fintype.card (GG g N) := Fintype.card_pos
  have hgpos : 0 < g := hg.out.pos
  set k : ℕ := (if L.sharp = true then L.k else 0) with hk
  rw [← hJ, ← hdim] at hG
  have he : L.e 1 = ((Nat.card {u // L.Mem u} : ℂ))⁻¹ := he1
  set J : ℕ := Nat.card {u // L.Mem u}
  set d : ℕ := Module.finrank ℂ V
  set T : ℕ := torusCard g f
  set r : ℕ := rk V.ρ L.e
  have hJ0 : J ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  have hd0 : d ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  refine ⟨(r : ℝ) / ((g : ℝ) ^ k * (T : ℝ)), ?_, ?_⟩
  · rw [← hchar, hz, he, hG]
    have a1 : (J : ℂ) ≠ 0 := by exact_mod_cast hJ0
    have a2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have a3 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have a4 : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  · have a3 : (0 : ℝ) < T := by exact_mod_cast hT
    have a4 : (0 : ℝ) < (g : ℝ) ^ k := by positivity
    rw [le_div_iff₀ (mul_pos a4 a3)]
    calc (1 - 1 / (g : ℝ)) * (T : ℝ)⁻¹ * ((g : ℝ) ^ k * T) = (1 - 1 / (g : ℝ)) * (g : ℝ) ^ k := by
          field_simp
      _ ≤ r := hr

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBoundStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_representation_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  first | exact @GlobalTheory.BadShare.series_weight_lower_bound | exact GlobalTheory.BadShare.series_weight_lower_bound | (intros; apply GlobalTheory.BadShare.series_weight_lower_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadLabelTupleWeightLeBound
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem conv_dirac_sub_sum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (b : G → ℂ) (x : G) :
    conv (dirac - ∑ i ∈ s, a i) b x = b x - ∑ i ∈ s, conv (a i) b x := by
  unfold conv dirac
  simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem sum_goodSet_le_one (g : ℕ) [Fact g.Prime] (N m : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ) :
    ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤ 1 := by
  have h1 : ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
      ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun F _ _ => ?_
    exact Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  refine h1.trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => sqSet g N) fun _ f => ((torusCard g f : ℝ))⁻¹]
  have h2 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  have h3 := mass_nonneg (g := g) N fun _ => True
  simp only [mass, Finset.filter_true] at h2 h3
  exact Finset.prod_le_one₀ (fun _ _ => h3) fun _ _ => h2

theorem badWeight_le : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  intro g _ N m q d ι _ L τ ch hN hP hτ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hg⟩ := hP
  have hS := GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge g N m q d ι ch hN hg ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hS1 := sum_goodSet_le_one g N m ι ch
  have hS0 : 0 ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ :=
    Finset.sum_nonneg fun F _ => Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  choose! w hw1 hw2 using fun v => GlobalTheory.T.series_representation_weight_lower_bound g N (L v) (τ v) (hτ v)
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨1 - ∑ F ∈ goodSet g N ch, ∏ v, w v (F v), ?_, ?_⟩
  · unfold eGood
    rw [conv_dirac_sub_sum]
    push_cast
    rw [sub_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [(tens_calculus ι (GG g N) (GG g N)).1]
    unfold tens
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => hw1 v (F v) (hmem F hF v)
  · have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_le
    have hg0 : (0 : ℝ) < g := by linarith
    have hinv : 1 / (g : ℝ) ≤ 1 := by rw [div_le_one hg0]; exact hg1
    have hinv0 : 0 ≤ 1 / (g : ℝ) := by positivity
    have hA : (1 - 1 / (g : ℝ)) ^ Fintype.card ι * ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
        ∑ F ∈ goodSet g N ch, ∏ v, w v (F v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun F hF => ?_
      rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => ?_) fun v _ => hw2 v (F v) (hmem F hF v)
      exact mul_nonneg (by linarith) (inv_nonneg.2 (Nat.cast_nonneg _))
    have hB : 1 - (Fintype.card ι : ℝ) / g ≤ (1 - 1 / (g : ℝ)) ^ Fintype.card ι := by
      have := one_add_mul_le_pow (a := -(1 / (g : ℝ))) (by linarith) (Fintype.card ι)
      rw [← sub_eq_add_neg] at this
      refine le_trans (le_of_eq ?_) this
      ring
    have hC : 0 ≤ (Fintype.card ι : ℝ) / g := by positivity
    have hD := mul_le_mul_of_nonneg_right hB hS0
    have hE := mul_le_mul_of_nonneg_left hS1 hC
    nlinarith

end GlobalTheory.BadShare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadLabelTupleWeightLeBoundStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badLabelTuple_weight_le_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  first | exact @GlobalTheory.BadShare.badWeight_le | exact GlobalTheory.BadShare.badWeight_le | (intros; apply GlobalTheory.BadShare.badWeight_le <;> assumption)
end

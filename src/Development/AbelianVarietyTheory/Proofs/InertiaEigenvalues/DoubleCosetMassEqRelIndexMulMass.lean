module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
noncomputable section
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]

def dcMapLe {Γ W K : Subgroup G} (hWK : W ≤ K) : DC Γ W → DC Γ K :=
  Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)

def dcOfCoset (Γ W K : Subgroup G) (t : G) : K ⧸ W.subgroupOf K → DC Γ W :=
  Quotient.lift (fun k : K => (Quotient.mk (dcSetoid Γ W) (t * k))) (by
    intro a b hab
    apply Quotient.sound
    have h := (QuotientGroup.leftRel_apply).1 hab
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨1, Γ.one_mem, (a : G)⁻¹ * b, by simpa using h, ?_⟩
    simp [mul_assoc])

theorem dcOfCoset_mk (Γ W K : Subgroup G) (t : G) (k : K) :
    dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) = Quotient.mk (dcSetoid Γ W) (t * k) := rfl

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

theorem fiber_card_mul_stabCard {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K) (t : G)
    (ht : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) (k : K) :
    Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} *
      stabCard Γ W (t * k) = stabCard Γ K t := by
  classical
  set A := {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}
  set B := {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)}
  set T := {δ : Γ // (t * k)⁻¹ * (δ : G) * (t * k) ∈ W}
  have hT : stabCard Γ W (t * k) = Nat.card T := rfl
  have hA : stabCard Γ K t = Nat.card A := rfl
  let φ : A → K := fun γ => ⟨t⁻¹ * (γ.1 : G) * t, γ.2⟩
  have hα : ∀ γ : A, dcOfCoset Γ W K t ((φ γ * k : K) : K ⧸ W.subgroupOf K) =
      dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
    intro γ
    rw [dcOfCoset_mk, dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨(γ.1 : G)⁻¹, Γ.inv_mem γ.1.2, 1, W.one_mem, ?_⟩
    simp [φ, mul_assoc]
  let α : A → B := fun γ => ⟨(φ γ * k : K), hα γ⟩
  have hsurj : Function.Surjective α := by
    rintro ⟨x, hx⟩
    induction x using QuotientGroup.induction_on with
    | H k' =>
      rw [dcOfCoset_mk, dcOfCoset_mk] at hx
      obtain ⟨γ, hγ, w, hw, e⟩ := Quotient.exact hx

      have hmem : t⁻¹ * γ⁻¹ * t ∈ K := by
        have : t⁻¹ * γ⁻¹ * t = (k' : G) * w * (k : G)⁻¹ := by
          have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
            calc (k : G) = t⁻¹ * (t * k) := by group
              _ = _ := by rw [e]; group
          rw [e']; group
        rw [this]
        exact K.mul_mem (K.mul_mem k'.2 (hWK hw)) (K.inv_mem k.2)
      refine ⟨⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩, ?_⟩
      apply Subtype.ext
      show ((φ _ * k : K) : K ⧸ W.subgroupOf K) = (k' : K ⧸ W.subgroupOf K)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
        calc (k : G) = t⁻¹ * (t * k) := by group
          _ = _ := by rw [e]; group
      have : ((φ ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩ * k)⁻¹ * k' : K) = (w⁻¹ : G) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [e']; group
      rw [this]; exact W.inv_mem hw
  have hfib : ∀ γ₀ : A, Nonempty ({γ : A // α γ = α γ₀} ≃ T) := by
    intro γ₀
    have key : ∀ γ : A, α γ = α γ₀ ↔ (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) ∈ W := by
      intro γ
      rw [Subtype.ext_iff]
      show ((φ γ * k : K) : K ⧸ W.subgroupOf K) = ((φ γ₀ * k : K) : K ⧸ W.subgroupOf K) ↔ _
      rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((φ γ₀ * k)⁻¹ * (φ γ * k) : K) : G) = (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]; group
      rw [this]
    refine ⟨{ toFun := fun γ => ⟨⟨(γ₀.1 : G)⁻¹ * γ.1.1, Γ.mul_mem (Γ.inv_mem γ₀.1.2) γ.1.1.2⟩, (key γ.1).1 γ.2⟩
              invFun := fun δ => ⟨⟨⟨(γ₀.1 : G) * δ.1, Γ.mul_mem γ₀.1.2 δ.1.2⟩, ?_⟩, ?_⟩
              left_inv := fun γ => by ext; simp
              right_inv := fun δ => by ext; simp }⟩
    · have h1 : t⁻¹ * ((γ₀.1 : G) * δ.1) * t =
          (t⁻¹ * γ₀.1 * t) * ((k : G) * ((t * k)⁻¹ * δ.1 * (t * k)) * (k : G)⁻¹) := by group
      rw [h1]
      exact K.mul_mem γ₀.2 (K.mul_mem (K.mul_mem k.2 (hWK δ.2)) (K.inv_mem k.2))
    · rw [key]
      simpa using δ.2
  have e : A ≃ B × T :=
    (Equiv.sigmaFiberEquiv α).symm.trans
      ((Equiv.sigmaCongrRight (fun b => by
          have hb := hsurj b
          exact Classical.choice (by
            obtain ⟨γ₀, hγ₀⟩ := hb
            subst hγ₀
            exact hfib γ₀))).trans (Equiv.sigmaEquivProd B T))
  rw [hT, hA, Nat.card_congr e, Nat.card_prod]

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass
open scoped BigOperators

theorem dcOfCoset_surj {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (d : DC Γ W) (hd : dcMapLe hWK d = Quotient.mk (dcSetoid Γ K) t) :
    ∃ k : K, d = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
  induction d using Quotient.inductionOn with
  | h g =>
    have h2 : (dcSetoid Γ K) g t := Quotient.exact hd
    obtain ⟨γ, hγ, κ, hκ, e⟩ := (dcSetoid Γ K).iseqv.symm h2
    refine ⟨⟨κ, hκ⟩, ?_⟩
    rw [dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨γ⁻¹, Γ.inv_mem hγ, 1, W.one_mem, ?_⟩
    simp [e, mul_assoc]

theorem dcMapLe_dcOfCoset {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (x : K ⧸ W.subgroupOf K) : dcMapLe hWK (dcOfCoset Γ W K t x) = Quotient.mk (dcSetoid Γ K) t := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [dcOfCoset_mk]
    apply Quotient.sound
    exact ⟨1, Γ.one_mem, (k : G)⁻¹, K.inv_mem k.2, by simp⟩

theorem mass_eq_relIndex_mul {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K)
    (hW : Finite (DC Γ W)) (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    W.relIndex K ≠ 0 ∧ mass Γ W = (W.relIndex K : ℚ) * mass Γ K := by
  classical
  haveI := hW
  haveI : Finite (DC Γ K) := finite_dc_of_le hWK

  have hfibre : ∀ d : DC Γ W, Finite {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K 1 x = d} := by
    intro d
    by_cases hne : ∃ x : K ⧸ W.subgroupOf K, dcOfCoset Γ W K 1 x = d
    · obtain ⟨x, rfl⟩ := hne
      induction x using QuotientGroup.induction_on with
      | H k =>
        have h1 := fiber_card_mul_stabCard Γ W K hWK 1 (hfin 1) k
        have h2 := stabCard_pos (Γ := Γ) (K := K) 1 (hfin 1)
        have h3 : 0 < Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)} := by
          rcases Nat.eq_zero_or_pos (Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)}) with h | h
          · rw [h, zero_mul] at h1; omega
          · exact h
        exact (Nat.card_pos_iff.1 h3).2
    · push_neg at hne
      exact Finite.of_injective (β := Empty) (fun x => (hne x.1 x.2).elim) (fun x => (hne x.1 x.2).elim)
  haveI : Finite (K ⧸ W.subgroupOf K) :=
    Finite.of_equiv _ (Equiv.sigmaFiberEquiv (dcOfCoset Γ W K 1))
  have hidx : W.relIndex K = Nat.card (K ⧸ W.subgroupOf K) := rfl
  have hne0 : W.relIndex K ≠ 0 := by
    rw [hidx]; exact Nat.card_ne_zero.2 ⟨⟨(1 : K)⟩, inferInstance⟩
  refine ⟨hne0, ?_⟩
  haveI := Fintype.ofFinite (DC Γ W)
  haveI := Fintype.ofFinite (DC Γ K)
  haveI := Fintype.ofFinite (K ⧸ W.subgroupOf K)

  have hfib : ∀ c : DC Γ K,
      ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c), ((stabCard Γ W d.out : ℕ) : ℚ)⁻¹ =
        (W.relIndex K : ℚ) * ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹ := by
    intro c
    set t := c.out with htdef
    have hct : c = Quotient.mk (dcSetoid Γ K) t := (Quotient.out_eq c).symm
    have hsK : (0 : ℚ) < stabCard Γ K t := by exact_mod_cast stabCard_pos t (hfin t)
    have hcard : (W.relIndex K : ℚ) = ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c),
        ((Finset.univ.filter (fun x => dcOfCoset Γ W K t x = d)).card : ℚ) := by
      rw [hidx, Nat.card_eq_fintype_card, ← Finset.card_univ]
      rw [Finset.card_eq_sum_card_fiberwise (f := dcOfCoset Γ W K t)
        (t := Finset.univ.filter (fun d => dcMapLe hWK d = c))]
      · push_cast; rfl
      · intro x _
        simp [dcMapLe_dcOfCoset, hct]
    rw [hcard, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨k, rfl⟩ := dcOfCoset_surj hWK t _ (hd.trans hct)
    have h1 := fiber_card_mul_stabCard Γ W K hWK t (hfin t) k
    rw [dcOfCoset_mk, stabCard_out]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← dcOfCoset_mk]
    have hsW : (0 : ℚ) < stabCard Γ W (t * k) := by
      have := stabCard_pos t (hfin t)
      rcases Nat.eq_zero_or_pos (stabCard Γ W (t * k)) with h | h
      · rw [h, mul_zero] at h1; omega
      · exact_mod_cast h
    have h1' : (Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x =
        dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} : ℚ) * stabCard Γ W (t * k) = stabCard Γ K t := by
      exact_mod_cast h1
    field_simp
    linarith [h1']
  unfold mass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (dcMapLe hWK)]
  exact Finset.sum_congr rfl (fun c _ => hfib c)

end GlobalTheory.UnimodMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMassStatement
open GlobalTheory.UnimodMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass : ∀ (G : Type) [Group G] (Γ W K : Subgroup G), W ≤ K → Finite (GlobalTheory.UnimodMass.DC Γ W) → (∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) → W.relIndex K ≠ 0 ∧ GlobalTheory.UnimodMass.mass Γ W = (W.relIndex K : ℚ) * GlobalTheory.UnimodMass.mass Γ K := by
  first | exact @GlobalTheory.UnimodMass.mass_eq_relIndex_mul | exact GlobalTheory.UnimodMass.mass_eq_relIndex_mul | (intros; apply GlobalTheory.UnimodMass.mass_eq_relIndex_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.SenAdd

section
variable {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

theorem pow_mem (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (m : ℕ) :
    ∀ y ∈ Q, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Q.sub_mem (hQ y hy) (Q.smul_mem _ hy)

theorem mem_gen (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (y : A) :
    y ∈ (⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m)) ↔
      ∃ m : ℕ, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  have hm : Monotone fun m : ℕ => Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) := by
    refine monotone_nat_of_le_succ fun m z hz => ?_
    rw [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]
    simpa using pow_mem T Q hQ x 1 _ hz
  exact Submodule.mem_iSup_of_directed _ hm.directed_le

theorem pow_comm (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B) (hT : ∀ y, h (T y) = T' (h y))
    (x : k) (m : ℕ) (y : A) :
    h (((T - algebraMap k (Module.End k A) x) ^ m) y) = ((T' - algebraMap k (Module.End k B) x) ^ m) (h y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp [Module.algebraMap_end_apply, hT]

theorem gmult_transport (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B)
    (hT : ∀ y, h (T y) = T' (h y)) (P Q : Submodule k A) (P' Q' : Submodule k B)
    (hP : ∀ y ∈ P, T y ∈ P) (hQP : Q ≤ P) (hQ' : ∀ y ∈ Q', T' y ∈ Q')
    (hmap : ∀ y ∈ P, h y ∈ P') (hker : ∀ y ∈ P, h y ∈ Q' ↔ y ∈ Q)
    (hsur : ∀ z ∈ P', ∃ y ∈ P, z - h y ∈ Q') (x : k) : gmult T P Q x = gmult T' P' Q' x := by
  have hQ : ∀ y ∈ Q, T y ∈ Q := fun y hy =>
    (hker _ (hP y (hQP hy))).1 (by rw [hT]; exact hQ' _ ((hker y (hQP hy)).2 hy))
  unfold gmult
  set G := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) with hG
  set G' := P' ⊓ ⨆ m : ℕ, Q'.comap ((T' - algebraMap k (Module.End k B) x) ^ m) with hG'
  have hGG : ∀ y ∈ G, h y ∈ G' := by
    rintro y ⟨hy, hy2⟩
    obtain ⟨m, hm⟩ := (mem_gen T Q hQ x y).1 hy2
    refine ⟨hmap y hy, (mem_gen T' Q' hQ' x _).2 ⟨m, ?_⟩⟩
    rw [← pow_comm T T' h hT]
    exact (hker _ (hQP hm)).2 hm
  let φ : G →ₗ[k] (G' ⧸ Q'.submoduleOf G') := (Q'.submoduleOf G').mkQ ∘ₗ h.restrict hGG
  have hk : Q.submoduleOf G = LinearMap.ker φ := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    change y ∈ Q ↔ Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hker y hy.1).symm
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, hy, hzy⟩ := hsur z hz.1
    obtain ⟨m, hm⟩ := (mem_gen T' Q' hQ' x z).1 hz.2
    have hyG : y ∈ G := by
      refine ⟨hy, (mem_gen T Q hQ x y).2 ⟨m, (hker _ (pow_mem T P hP x m y hy)).1 ?_⟩⟩
      rw [pow_comm T T' h hT]
      have := Q'.sub_mem hm (pow_mem T' Q' hQ' x m _ hzy)
      rwa [map_sub, sub_sub_cancel] at this
    refine ⟨⟨y, hyG⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [eq_comm, Submodule.Quotient.eq]
    exact hzy
  rw [hk]
  exact (φ.quotKerEquivOfSurjective hs).finrank_eq

end

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]


omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_one_le (N : Submodule k⟦X⟧ V) : sh 1 N ≤ N := by
  have := sh_le_sh_of_le (zero_le_one' ℤ) N
  rwa [sh_zero_eq] at this

theorem nab_mem_sh_one {l : ℕ} (R : RingPG k l) (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V)
    (hN : CondC g N) : ∀ y ∈ sh 1 N, nab g y ∈ sh 1 N := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  have hv := vv_ne_zero k
  have h1 := hN z hz
  have h2 : g z ∈ N := by simpa using N.add_mem (sh_one_le N h1) hz
  have h3 : vv k ^ (1 : ℤ) • (κ • g z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem κ h2, rfl⟩
  have h4 : nab g (vv k ^ (1 : ℤ) • z) = (g z - z) - vv k ^ (1 : ℤ) • (κ • g z) := by
    rw [nab_apply_eq, zpow_one, hg, hκ, ← algebraMap_smul k⸨X⸩ κ, mul_smul, ← smul_sub, inv_smul_smul₀ hv,
      sub_smul, one_smul, smul_smul, mul_comm (vv k)]
    change g z - ((κ : k⸨X⸩) * vv k) • g z - z = g z - z - ((κ : k⸨X⸩) * vv k) • g z
    abel
  rw [h4]
  exact Submodule.sub_mem _ h1 h3


omit [IsScalarTower k k⸨X⸩ V] in
theorem finite_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    FiniteDimensional k (↥(N.restrictScalars k) ⧸
      ((sh 1 N).restrictScalars k).submoduleOf (N.restrictScalars k)) := by
  obtain ⟨s, hs⟩ := hN
  have hle : Submodule.span k (s : Set V) ≤ N.restrictScalars k :=
    Submodule.span_le.2 fun y hy => hs ▸ Submodule.subset_span hy
  have key : ∀ y ∈ N, ∃ z ∈ Submodule.span k (s : Set V), y - z ∈ sh 1 N := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨z, hz, h⟩ := hy
      obtain ⟨z', hz', h'⟩ := hy'
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      have := Submodule.add_mem _ h h'
      rwa [sub_add_sub_comm] at this
    | smul a y _ hy =>
      obtain ⟨z, hz, h⟩ := hy
      refine ⟨PowerSeries.constantCoeff a • z, Submodule.smul_mem _ _ hz, ?_⟩
      set t : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
      have ha : a = PowerSeries.X * t + algebraMap k k⟦X⟧ (PowerSeries.constantCoeff a) :=
        PowerSeries.eq_X_mul_shift_add_const a
      have h3 : vv k ^ (1 : ℤ) • (t • z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem t (hle hz), rfl⟩
      have h4 : vv k ^ (1 : ℤ) • (t • z) = (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [zpow_one, mul_smul, vv_eq_coe_X]
        exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) (t • z)
      have h5 : a • y - PowerSeries.constantCoeff a • z = a • (y - z) + (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [← algebraMap_smul k⟦X⟧ (PowerSeries.constantCoeff a) z, eq_sub_of_add_eq ha.symm, smul_sub, sub_smul]
        abel
      rw [h5]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h) (h4 ▸ h3)
  haveI : FiniteDimensional k (Submodule.span k (s : Set V)) := FiniteDimensional.span_finset k s
  refine Module.Finite.of_surjective (Submodule.mkQ _ ∘ₗ Submodule.inclusion hle) fun w => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨z, hz, h⟩ := key y hy
  refine ⟨⟨z, hz⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [eq_comm, Submodule.Quotient.eq]
  exact h

end

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] {U : Type} [AddCommGroup U] [Module k⸨X⸩ U] [Module k⟦X⟧ U] [Module k U] [IsScalarTower k⟦X⟧ k⸨X⸩ U] [IsScalarTower k k⸨X⸩ U] [IsScalarTower k k⟦X⟧ U] [FiniteDimensional k⸨X⸩ U] (gV : V →ₗ[k] V) (gW : W →ₗ[k] W) (gU : U →ₗ[k] U) (f : W →ₗ[k⸨X⸩] V) (p : V →ₗ[k⸨X⸩] U), Semi R.γ gV → Function.Injective f → Function.Surjective p → Function.Exact f p → (∀ x, f (gW x) = gV (f x)) → (∀ x, p (gV x) = gU (p x)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC gV N → ∀ x : k, sen gV N x = sen gW (N.comap (f.restrictScalars k⟦X⟧)) x + sen gU (N.map (p.restrictScalars k⟦X⟧)) x := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ U _ _ _ _ _ _ _ _ gV gW gU f p hg _ _ hex hf hp N hN hC x
  have hN1 := (condC_iff_nab_mem gV N).1 hC
  have hN2 := nab_mem_sh_one R gV hg N hC
  have nf : ∀ y, f (nab gW y) = nab gV (f y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hf]
  have np : ∀ y, p (nab gV y) = nab gU (p y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hp]
  set N' := N.map (p.restrictScalars k⟦X⟧) with hN'
  have hsh : ∀ u, u ∈ sh 1 N' ↔ ∃ y ∈ sh 1 N, p y = u := by
    intro u
    constructor
    · intro hu
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hu
      exact ⟨_, mem_sh_iff_exists.2 ⟨z, hz, rfl⟩, map_smul p _ _⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
      exact mem_sh_iff_exists.2 ⟨p z, ⟨z, hz, rfl⟩, (map_smul p _ _).symm⟩
  have hU : ∀ u ∈ sh 1 N', nab gU u ∈ sh 1 N' := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hsh u).1 hu
    exact (hsh _).2 ⟨_, hN2 y hy, np y⟩
  let Q : Submodule k V := N.restrictScalars k ⊓ ((sh 1 N').restrictScalars k).comap (p.restrictScalars k)
  have hQ : ∀ y, y ∈ Q ↔ y ∈ N ∧ p y ∈ sh 1 N' := fun _ => Iff.rfl
  have hadd := GlobalTheory.PhiGam.GmultAdd.main (nab gV) (N.restrictScalars k) Q ((sh 1 N).restrictScalars k)
    (fun y hy => (hQ y).2 ⟨sh_one_le N hy, (hsh _).2 ⟨y, hy, rfl⟩⟩) inf_le_left hN1
    (fun y hy => (hQ _).2 ⟨hN1 y hy.1, by rw [np]; exact hU _ hy.2⟩) hN2 (finite_quot N hN.1) x
  have e1 : gmult (nab gV) (N.restrictScalars k) Q x = sen gU N' x :=
    gmult_transport (nab gV) (nab gU) (p.restrictScalars k) np _ _ (N'.restrictScalars k)
      ((sh 1 N').restrictScalars k) hN1 inf_le_left hU
      (fun y hy => ⟨y, hy, rfl⟩) (fun y hy => ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩)
      (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩) x
  have e2 : sen gW (N.comap (f.restrictScalars k⟦X⟧)) x = gmult (nab gV) Q ((sh 1 N).restrictScalars k) x := by
    refine gmult_transport (nab gW) (nab gV) (f.restrictScalars k) nf _ _ _ _ ?_ (sh_one_le _) hN2 ?_ ?_ ?_ x
    · intro y hy
      change f (nab gW y) ∈ N
      rw [nf]
      exact hN1 _ hy
    · intro y hy
      refine (hQ _).2 ⟨hy, ?_⟩
      change p (f y) ∈ _
      rw [hex.apply_apply_eq_zero]
      exact Submodule.zero_mem _
    · intro y _
      change f y ∈ sh 1 N ↔ y ∈ sh 1 _
      rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]
      rfl
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := (hsh _).1 hz.2
      obtain ⟨w, hw⟩ := (hex (z - y)).1 (by rw [map_sub, hyz]; exact sub_self _)
      refine ⟨w, ?_, ?_⟩
      · change f w ∈ N
        rw [hw]
        exact N.sub_mem hz.1 (sh_one_le N hy)
      · change z - f w ∈ sh 1 N
        rwa [hw, sub_sub_cancel]
  rw [e2, ← e1, add_comm]
  exact hadd

end GlobalTheory.PhiGam.SenAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSum
open GlobalTheory.PMonE

open Finset
namespace GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

noncomputable abbrev frobAut : RingAut F := frobeniusEquiv F p

theorem frob_pow_apply (n : ℕ) (x : F) : ((frobAut (F := F) p) ^ n) x = x ^ p ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih]
    simp only [frobAut, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
    rw [mul_comm]

theorem frob_inv_pow_apply (n : ℕ) (x : F) :
    (((frobAut (F := F) p)⁻¹) ^ n) x = ((frobeniusEquiv F p).symm)^[n] x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply, RingAut.mul_apply, ih, RingAut.inv_apply]

theorem pw_eq (k : ℤ) (x : F) : pw p k x = ((frobAut (F := F) p) ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frob_pow_apply]
    simp
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.mp hk))
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, frob_inv_pow_apply]
    simp

theorem pw_mul (k : ℤ) (a b : F) : pw p k (a * b) = pw p k a * pw p k b := by
  rw [pw_eq, pw_eq, pw_eq, map_mul]

theorem pw_win (h r L : ℕ) (hr : r ≤ h) (hL : 1 ≤ L) (n : ℤ) (hn : -(L : ℤ) ≤ n) (z : F) :
    pw p ((r : ℤ) + n * h) (z ^ (p ^ h) ^ (L - 1)) ^ p ^ (h - r) = z ^ (p ^ h) ^ ((n + L).toNat) := by
  have e1 : z ^ (p ^ h) ^ (L - 1) = ((frobAut (F := F) p) ^ (((h * (L - 1) : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e2 : z ^ (p ^ h) ^ ((n + L).toNat) =
      ((frobAut (F := F) p) ^ (((h * (n + L).toNat : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e3 : ∀ y : F, y ^ p ^ (h - r) = ((frobAut (F := F) p) ^ (((h - r : ℕ)) : ℤ)) y := fun y => by
    rw [zpow_natCast, frob_pow_apply]
  rw [e3, pw_eq, e1, e2, ← RingAut.mul_apply, ← RingAut.mul_apply, ← zpow_add, ← zpow_add]
  congr 2
  have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
  push_cast [Nat.cast_sub hr, Nat.cast_sub hL, ht]
  ring

end GlobalTheory.PMonE.WinCoef


open GlobalTheory.PMonE.WinCoef in
theorem GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ) : 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h),
    (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) =
      gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  intro hL z r
  have hr : (r : ℕ) ≤ h := r.isLt.le
  simp only [rowS, winPt, gsum, Finset.sum_apply, Matrix.mulVec, dotProduct, coefB, Matrix.of_apply]
  rw [Finset.sum_comm (s := Finset.range (L + U + 1)), Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_nbij' (fun n => (n + L).toNat) (fun m => (m : ℤ) - L) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    omega
  · intro m hm
    simp
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
    have hle : (n + L).toNat ≤ L + U := by omega
    have hsub : (((n + L).toNat : ℕ) : ℤ) - L = n := by omega
    rw [if_pos hle, hsub, term, term, winPt, pw_mul, ← pw_win p h r L hr hL n hn.1 (z j)]
    rw [show lam j * ϖ ^ (-n) * (pw p (↑↑r + n * ↑h) (π j) * pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1))) /
        (lam r * π r ^ p ^ (r : ℕ)) = (lam j * ϖ ^ (-n) * pw p (↑↑r + n * ↑h) (π j) / (lam r * π r ^ p ^ (r : ℕ))) *
        pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1)) by ring, mul_pow]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSumStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F) (L U : ℕ), 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h), (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) = gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  first | exact @GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | exact GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | (intros; apply GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralRightCosetFunEqFinsum
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory

theorem integral_rightCoset_fun_eq_finsum (G Λ : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (H : Set G)
    (hH : IsOpen H) (hμ : μ H = 1) (π : G → Λ) (hπ : ∀ g g', π g' = π g ↔ g' * g⁻¹ ∈ H)
    (s : Λ → ℂ) (hs : ∀ l, s l = 0 ∨ ‖s l‖ = 1) :
    ∫ g, s (π g) ∂μ = ∑ᶠ l ∈ Set.range π, s l := by
  classical

  have hfib : ∀ g, π ⁻¹' {π g} = (fun x => x * g⁻¹) ⁻¹' H := by
    intro g; ext x; simp [hπ g x]
  have hfibO : ∀ g, IsOpen (π ⁻¹' {π g}) := by
    intro g; rw [hfib g]; exact hH.preimage (continuous_mul_const _)
  have hfibM : ∀ l, MeasurableSet (π ⁻¹' {l}) := by
    intro l
    by_cases hl : l ∈ Set.range π
    · obtain ⟨g, rfl⟩ := hl; exact (hfibO g).measurableSet
    · have : π ⁻¹' {l} = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hl ⟨x, h⟩
      rw [this]; exact MeasurableSet.empty
  have hfib1 : ∀ g, μ (π ⁻¹' {π g}) = 1 := by
    intro g; rw [hfib g, measure_preimage_mul_right, hμ]
  set S := Set.range π ∩ Function.support s with hSdef
  by_cases hS : S.Finite
  · set T := hS.toFinset with hT
    have hfun : (fun g => s (π g)) = fun g => ∑ l ∈ T, (π ⁻¹' {l}).indicator (fun _ => s l) g := by
      funext g
      have : ∀ l, (π ⁻¹' {l}).indicator (fun _ => s l) g = if π g = l then s (π g) else 0 := by
        intro l
        by_cases h : π g = l
        · subst h; simp
        · simp [Set.indicator_apply, h]
      simp only [this, Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · have : π g ∉ S := by rw [hT, Set.Finite.mem_toFinset] at *; exact h
        by_contra hne
        exact this ⟨⟨g, rfl⟩, Ne.symm hne |>.symm⟩
    rw [hfun, MeasureTheory.integral_finsetSum]
    · rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hS]
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [integral_indicator_const _ (hfibM l)]
      have hl' : l ∈ Set.range π := ((Set.Finite.mem_toFinset hS).1 hl).1
      obtain ⟨g, rfl⟩ := hl'
      simp [Measure.real, hfib1 g]
    · intro l _
      exact (integrable_indicator_iff (hfibM l)).2 (by
        by_cases hl : l ∈ Set.range π
        · obtain ⟨g, rfl⟩ := hl
          haveI : IsFiniteMeasure (μ.restrict (π ⁻¹' {π g})) := ⟨by simp [hfib1 g]⟩
          exact integrable_const _
        · have : π ⁻¹' {l} = ∅ := by
            ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
            exact fun h => hl ⟨x, h⟩
          rw [this]; exact integrableOn_empty)
  · rw [finsum_mem_eq_zero_of_infinite hS]
    apply integral_undef
    intro hint
    have hfin := hint.2

    have hbound : ∀ F : Finset Λ, (↑F : Set Λ) ⊆ S → (F.card : ENNReal) ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
      intro F hF
      calc (F.card : ENNReal) = ∑ l ∈ F, μ (π ⁻¹' {l}) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro l hl
            obtain ⟨⟨g, rfl⟩, _⟩ := hF hl
            simp [hfib1 g]
        _ = ∫⁻ g, ∑ l ∈ F, (π ⁻¹' {l}).indicator 1 g ∂μ := by
            rw [MeasureTheory.lintegral_finsetSum]
            · refine Finset.sum_congr rfl ?_
              intro l _
              rw [lintegral_indicator_one (hfibM l)]
            · intro l _
              exact (measurable_one.indicator (hfibM l))
        _ ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
            apply lintegral_mono
            intro g
            have : ∀ l, (π ⁻¹' {l}).indicator (1 : G → ENNReal) g = if π g = l then 1 else 0 := by
              intro l; simp [Set.indicator_apply]
            simp only [this, Finset.sum_ite_eq]
            split_ifs with h
            · obtain ⟨_, hsupp⟩ := hF h
              rcases hs (π g) with h0 | h1
              · exact absurd h0 hsupp
              · rw [← ofReal_norm_eq_enorm, h1]; simp
            · exact bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq (hS : S.Infinite) n
    have := hbound F hFS
    rw [hFc] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)

end GlobalTheory
end

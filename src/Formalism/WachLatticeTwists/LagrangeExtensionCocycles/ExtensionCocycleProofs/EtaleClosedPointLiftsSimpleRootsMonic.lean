module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.CoboundaryTransfers.WachBridges
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.UnitLemmaCaseALevelZero

@[expose] public section

section -- merged from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.LiftExistsSecondCase
section -- merged from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.GrothendieckTopDegree
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

theorem lift_to_subgroup_exists : StatLiftSub := by
  unfold StatLiftSub
  intro ℓ _ H₁ H₂ H₁' H₂' _ _ _ _ _ _ _ _ Hf₁ Hf₂ Hf₁' Hf₂' h h' res₂ cor₁ cor₂ g E hg hcr hcomm hres hcor hlift κ' hκ'
  obtain ⟨κ₁, hκ₁, he⟩ := hlift (res₂ κ') (hres κ' hκ')
  set v := padicValNat ℓ g with hv
  obtain ⟨m, hm⟩ : ℓ ^ v ∣ g := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hcop : ¬ ℓ ∣ m := by
    intro hdvd
    have h5 : ℓ ^ (v + 1) ∣ g := by
      rw [hm, pow_succ]
      exact mul_dvd_mul_left _ hdvd
    exact pow_succ_multiplicity_not_dvd (p := ℓ) (n := g) (Nat.ne_of_gt hg) (by simpa [hv, Nat.padicValNat_def] using h5)
  have hu : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((m : ℤ) : ℤ_[ℓ])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      exact_mod_cast hcop
    have h3 : ((m : ℤ) : ℤ_[ℓ]) = (m : ℤ_[ℓ]) := Int.cast_natCast m
    rw [← h3]
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨(↑hu.unit⁻¹ : ℤ_[ℓ]) • cor₁ κ₁, Hf₁'.smul_mem _ (hcor κ₁ hκ₁), ?_⟩
  rw [map_smul, hcomm, he, map_smul, hcr, smul_smul, smul_smul]
  congr 1
  have hg' : (g : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ v * (m : ℤ_[ℓ]) := by
    rw [hm]
    push_cast
    ring
  have hum : (↑hu.unit⁻¹ : ℤ_[ℓ]) * (m : ℤ_[ℓ]) = 1 := hu.val_inv_mul
  rw [hg', pow_add]
  linear_combination (ℓ : ℤ_[ℓ]) ^ E * (ℓ : ℤ_[ℓ]) ^ v * hum

theorem regulator_bound_for_x : StatRegX := by
  unfold StatRegX
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg y hy hX
  unfold RegXQ at hreg
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → B.X • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg (B.X • z) hXz ⟨B.Q • z, hQ, by rw [smul_smul, smul_smul, mul_comm]⟩
    have h0 : B.X • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := W.X_inj _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

theorem regulator_bound_for_l : StatRegL := by
  unfold StatRegL
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg htor y hy hX
  unfold RegLQ at hreg
  unfold NoTors at htor
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → (ℓ : ℤ_[ℓ]) • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg ((ℓ : ℤ_[ℓ]) • z) hXz ⟨B.Q • z, hQ, smul_comm _ _ _⟩
    have h0 : (ℓ : ℤ_[ℓ]) • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := htor _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

theorem extension_class_is_cocycle : StatExtCocycle := by
  unfold StatExtCocycle
  intro ℓ _ A _ _ B M D _ _ _ _ W H _ _ cl κ E e hD hlift
  obtain ⟨x, hxN, hx⟩ := hlift E.e E.e_mem
  have hπφ : E.S.π.f (E.Wp.φ x - x) = 0 := by
    rw [map_sub, E.S.π.φ_comm, hx, map_smul, E.φe, sub_self]
  have hπγ : E.S.π.f (E.Wp.γ x - x) = 0 := by
    rw [map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨y, hy⟩ := (E.S.exact _).1 hπφ
  obtain ⟨z, hz⟩ := (E.S.exact _).1 hπγ
  have hd : (W.γ y - y) - (W.φ z - z) = 0 := by
    apply E.S.ι_inj
    simp only [map_sub, map_zero, E.S.ι.γ_comm, E.S.ι.φ_comm, hy, hz, E.Wp.comm]
    abel
  have hZ : ((y, z) : D × D) ∈ W.Z1 := by
    show ((y, z) : D × D) ∈ LinearMap.ker ((W.γ - LinearMap.id).coprod (-(W.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = (W.γ y - y) - (W.φ z - z) := by abel
      _ = 0 := hd
  have hQ : B.Q ^ M • y ∈ W.N := by
    apply E.S.sat
    rw [map_smul, hy, smul_sub]
    exact E.Wp.N.sub_mem (E.Wp.φ_N x hxN) (E.Wp.N.smul_mem _ hxN)
  obtain ⟨x', hx'N, hx'⟩ := E.Wp.γ_N x hxN
  have hπx' : E.S.π.f x' = 0 := by
    apply E.Wt.X_inj
    rw [← map_smul, ← hx', map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨x₀, hx₀⟩ := (E.S.exact x').1 hπx'
  have hx₀N : x₀ ∈ W.N := E.S.sat x₀ (by rw [hx₀]; exact hx'N)
  have hzX : z = B.X • x₀ := by
    apply E.S.ι_inj
    rw [map_smul, hx₀, hz, hx']
  refine ⟨⟨(y, z), hZ⟩, ?_, ?_⟩
  · unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    exact ⟨⟨hQ, x₀, hx₀N, hzX⟩, hd⟩
  · exact hD ((ℓ : ℤ_[ℓ]) ^ e) x ⟨(y, z), hZ⟩ hx hy hz

theorem rational_points_map_surjective : StatRatSurj := by
  unfold StatRatSurj
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g e₁ hp hnat hcoc hherr honto hlift
  unfold Formalism.CoboundaryTransfers.RatSurj
  intro y z hyz
  have memZ : ∀ a b : D₂, W₂.γ a - a - (W₂.φ b - b) = 0 → ((a, b) : D₂ × D₂) ∈ W₂.Z1 := by
    intro a b h
    show ((a, b) : D₂ × D₂) ∈ LinearMap.ker ((W₂.γ - LinearMap.id).coprod (-(W₂.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = W₂.γ a - a - (W₂.φ b - b) := by abel
      _ = 0 := h
  have hyz' := hyz
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hyz'
  obtain ⟨⟨hQ₂, n₂, hn₂, hz₂⟩, hd₂⟩ := hyz'
  have hκ : cl₂ ⟨(y, z), memZ y z hd₂⟩ ∈ Hf₂ := hcoc _ hyz
  obtain ⟨k, κ₁, hκ₁, hgk⟩ := honto _ hκ
  obtain ⟨⟨⟨y₁, z₁⟩, hZ₁⟩, hpr₁c, hpr₁⟩ := hlift κ₁ hκ₁
  have hc₁ := hpr₁c
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hc₁
  obtain ⟨⟨hQ₁', n₁, hn₁, hz₁'⟩, hd₁'r⟩ := hc₁
  have hz₁ : z₁ = B.X • n₁ := hz₁'
  have hd₁ : W₁.γ y₁ - y₁ - (W₁.φ z₁ - z₁) = 0 := hd₁'r
  have hQ₁ : B.Q ^ M • y₁ ∈ W₁.N := hQ₁'
  have hd₁' : W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁) = 0 := by
    have h := congrArg S.π.f hd₁
    simpa [map_sub, S.π.γ_comm, S.π.φ_comm] using h
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ], c = (ℓ : ℤ_[ℓ]) ^ (e₁ + k) := ⟨_, rfl⟩
  have hcP : W₂.Cocycle (S.π.f y₁ - c • y) (S.π.f z₁ - c • z) := by
    unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    refine ⟨⟨?_, S.π.f n₁ - c • n₂, W₂.N.sub_mem (S.π.N_le _ hn₁) (W₂.N.smul_of_tower_mem c hn₂), ?_⟩, ?_⟩
    · rw [smul_sub, ← map_smul, smul_comm (B.Q ^ M) c y]
      exact W₂.N.sub_mem (S.π.N_le _ hQ₁) (W₂.N.smul_of_tower_mem c hQ₂)
    · rw [hz₁, hz₂, map_smul, smul_sub, smul_comm c B.X n₂]
    · calc W₂.γ (S.π.f y₁ - c • y) - (S.π.f y₁ - c • y) - (W₂.φ (S.π.f z₁ - c • z) - (S.π.f z₁ - c • z))
          = (W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁)) -
              c • (W₂.γ y - y - (W₂.φ z - z)) := by
            rw [map_sub, map_sub, map_smul, map_smul]
            simp only [smul_sub]
            abel
        _ = 0 := by rw [hd₁', hd₂, smul_zero, sub_zero]
  have hcl : cl₂ (⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩ - c • ⟨(y, z), memZ y z hd₂⟩) = 0 := by
    rw [map_sub, map_smul, ← hnat ⟨(y₁, z₁), hZ₁⟩ ⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩
      (by first | rfl | simp [Formalism.CoboundaryTransfers.Hom.f2]), hpr₁, map_smul, hgk, hc, pow_add, mul_smul, sub_self]
  have hcob := hherr _ hcP hcl
  unfold WachMod.IsCob1 at hcob
  obtain ⟨x, hxN, hx1, hx2⟩ := hcob
  change S.π.f y₁ - c • y = W₂.φ x - x at hx1
  change S.π.f z₁ - c • z = W₂.γ x - x at hx2
  refine ⟨e₁ + k, y₁, z₁, hpr₁c, x, hxN, ?_, ?_⟩
  · rw [hp, ← hc, ← hx1]
    abel
  · rw [hp, ← hc, ← hx2]
    abel

end Formalism.RepresentationBoundsCohomology.N2
end
end

section -- merged from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.PhiOnto
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Formalism.CoboundaryTransfers

theorem phi_map_surjective : StatPhiOnto := by
  intro O A _ _ _ B M D _ _ _ _ W I _ k b hk hMb hQI hφI n hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ : ∃ d, k * b = M + 1 + d := ⟨k * b - (M + 1), by omega⟩

  have hmem : ∀ x : W.N, (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)) ∈ W.N :=
    fun x => W.N.smul_mem _ (W.φ_N x x.2)
  let g : W.N →+ W.N :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hg : ∀ x : W.N, W.φ (B.X ^ b • (x : D)) = B.X ^ b • ((g x : W.N) : D) := by
    intro x
    show _ = B.X ^ b • ((B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)))
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul]
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, hd]
    ring
  have hφpow : ∀ (j : ℕ) (r : A), r ∈ I ^ j → B.φ r ∈ I ^ j := by
    intro j r hr
    have h1 : Ideal.map (B.φ : A →+* A) I ≤ I :=
      Ideal.map_le_iff_le_comap.2 (fun a ha => hφI a ha)
    have h2 : (B.φ : A →+* A) r ∈ Ideal.map (B.φ : A →+* A) (I ^ j) := Ideal.mem_map_of_mem _ hr
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 j h2
  have hcontr : ∀ j : ℕ, ∀ x ∈ (I ^ j • ⊤ : Submodule A W.N), g x ∈ (I ^ (j + 1) • ⊤ : Submodule A W.N) := by
    intro j x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      have e : g (r • m) = (B.φ r * B.Q) •
          (⟨(B.Q ^ d * v ^ b) • (B.Q ^ M • W.φ (m : D)), W.N.smul_mem _ (W.φ_N m m.2)⟩ : W.N) := by
        ext
        show (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (r • (m : D))) = _
        rw [W.φ_smul]
        simp only [SetLike.mk_smul_mk, smul_smul]
        congr 1
        ring
      rw [e]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hφpow j r hr) hQI
    · intro x y hx hy
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  have hbij := _root_.subIdBijectiveOfContracting_holds A W.N I g hcontr
  obtain ⟨z, hz⟩ := hbij.2 (-(⟨n, hn⟩ : W.N))
  refine ⟨z, z.2, ?_⟩
  rw [hg z, ← smul_sub]
  congr 1
  have : ((g z - z : W.N) : D) = -n := by
    have := congrArg (fun t : W.N => (t : D)) hz
    simpa using this
  have h3 : ((g z : W.N) : D) - (z : D) = -n := by simpa using this
  rw [← neg_sub, h3, neg_neg]

end Formalism.RepresentationBoundsCohomology.N2
end
end

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']

def gbase (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (h : B.GammaX (u : ℤ_[ℓ])) : GBase ℓ A :=
  { γ := B.γ, X := B.X, u := u, γX := h }

def pairOfHom {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) : GPair (gbase B u h) D' :=
  { N := W'.N
    N' := W.N.map F.f
    le := by rintro _ ⟨x, hx, rfl⟩; exact F.N_le x hx
    γ := W'.γ
    γ_smul := W'.γ_smul
    X_inj := W'.X_inj
    γ_N := W'.γ_N
    γ_N' := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨x', hx', h⟩ := W.γ_N x hx
      exact ⟨F.f x', ⟨x', hx', rfl⟩, by rw [← F.γ_comm, ← map_sub, h, map_smul]; rfl⟩ }

theorem kills_iff {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (a : A) :
    (pairOfHom F u h).Kills a ↔ ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = a • n := by
  constructor
  · intro hk n hn
    obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.1 (hk n hn)
    exact ⟨x, hx, hfx⟩
  · intro h' n hn
    obtain ⟨x, hx, hfx⟩ := h' n hn
    exact Submodule.mem_map.2 ⟨x, hx, hfx⟩

theorem natCast_pow_smul (e : ℕ) (n : D) : ((ℓ : A) ^ e) • n = ((ℓ : ℤ_[ℓ]) ^ e) • n := by
  rw [← map_natCast (algebraMap ℤ_[ℓ] A), ← map_pow, algebraMap_smul]

theorem homKillsB {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (s a : ℕ) (hs : 1 ≤ s) (h2 : ℓ = 2 → 2 ≤ s)
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hK : XKills F a) :
    ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = ((ℓ : ℤ_[ℓ]) ^ eWB ℓ a s) • n := by
  have := unit_lemma_case_b_holds ℓ A (gbase B u h) D' (pairOfHom F u h) s a hs h2 hv ((kills_iff F u h _).2 hK)
  intro n hn
  obtain ⟨n₁, hn₁, e⟩ := (kills_iff F u h _).1 this n hn
  exact ⟨n₁, hn₁, by rw [e, natCast_pow_smul]⟩

theorem aeval_mem (N : Submodule ℤ_[ℓ] D) (γ : D →ₗ[ℤ_[ℓ]] D) (h : ∀ n ∈ N, γ n ∈ N)
    (R : ℤ_[ℓ][X]) : ∀ n ∈ N, aeval γ R n ∈ N := by
  induction R using Polynomial.induction_on with
  | C a =>
    intro n hn
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact N.smul_mem a hn
  | add p q hp hq =>
    intro n hn
    rw [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem (hp n hn) (hq n hn)
  | monomial k a ih =>
    intro n hn
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (h n hn)

theorem zero_notMem_JSet (jumps : Finset ℤ) (M : ℕ) : (0 : ℤ) ∉ JSet jumps M := by
  simp [JSet]

theorem eigSet_subset (jumps : Finset ℤ) (M : ℕ) : eigSet jumps M ⊆ insert 0 (JSet jumps M) := by
  intro x hx
  by_cases h0 : x = 0
  · exact Finset.mem_insert.2 (Or.inl h0)
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨h0, hx⟩))))

theorem prod_eig_dvd (jumps : Finset ℤ) (M : ℕ) (f : ℤ → ℤ_[ℓ][X]) :
    (∏ j ∈ eigSet jumps M, f j) ∣ f 0 * ∏ j ∈ JSet jumps M, f j := by
  have h := Finset.prod_dvd_prod_of_subset _ _ f (eigSet_subset jumps M)
  rwa [Finset.prod_insert (zero_notMem_JSet jumps M)] at h

end

theorem lift_exists_second_case : StatLiftB := by
  intro ℓ _ A _ _ B M u s H jumps hp hφX hγX hγQ hs h2 hv D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hQI hφI hRX hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO
  set eW := eWB ℓ H s with heW

  have hCK : CokerKilled S eW := by
    intro n hn
    rw [hp]
    exact homKillsB S.π u hγX s H hs h2 hv hXK n hn

  have hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE1 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)
  have hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧
      cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE2 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)

  have hRS : RatSurj S :=
    rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁

  have h1 := phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I 1 (M + 1) ⟨1, by rw [hφX]; ring⟩ (by omega) hQI hφI

  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], W₀.γ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : W₀.γ n = n + B.X • x' := by rw [← h]; abel
    rw [this]
    exact W₀.N.add_mem hn (W₀.N.smul_mem _ hx')
  have h3 : ∀ y, W₀.QInv y → aeval W₀.γ ((X - 1) *
      ∏ j ∈ JSet jumps M, (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R, hR⟩ := prod_eig_dvd jumps M (fun j => (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))))
    have e0 : (X - C (((u ^ (-(0 : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) : ℤ_[ℓ][X]) = X - 1 := by simp
    simp only [e0] at hR
    rw [hR, mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_mem _ W₀.γ hstab R _ (hSemi y hy)
  have hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + Formalism.LIFT.eU ℓ M s (JSet jumps M))) :=
    wachLatticeUnramified_statement ℓ A B M u hp hφX hγX hγQ D₀ D₁ D₂ W₀ W₁ W₂ S eW s (JSet jumps M) hs h2 hv
      (zero_notMem_JSet jumps M) h1 (regulator_bound_for_x ℓ A B M D₀ W₀ hRX) h3
      (regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT) hCK hRS
  intro κ hκ
  obtain ⟨κ₁, hκ₁, h⟩ := finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _
    hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ
  refine ⟨κ₁, hκ₁, ?_⟩
  rw [h, hp, ← pow_add]
  congr 2
  simp only [eUB, Formalism.LIFT.eU]
  ring

end Formalism.RepresentationBoundsCohomology.N2
end
end

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D₀ D₁ D₂ : Type}
  [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
  [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
  [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
  {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂}

theorem lifts_of_dvd (S : SES W₀ W₁ W₂) {c c' : ℤ_[ℓ]} (h : c ∣ c') (hL : Lifts S c) :
    Lifts S c' := by
  obtain ⟨d, rfl⟩ := h
  intro y z hyz
  obtain ⟨y₁, z₁, hc, hy, hz⟩ := hL y z hyz
  refine ⟨d • y₁, d • z₁, W₁.cocycle_smulO d hc, ?_, ?_⟩
  · rw [LinearMap.map_smul_of_tower, hy, smul_smul, mul_comm]
  · rw [LinearMap.map_smul_of_tower, hz, smul_smul, mul_comm]

theorem homKillsA (hℓ : ℓ ≠ 2) {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (u₁ : ℤ_[ℓ]ˣ) (h : B.GammaX (u₁ : ℤ_[ℓ])) (H : ℕ)
    (hv : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1) (hK : XKills F ((H + (ℓ - 2)) / (ℓ - 1))) :
    ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = ((ℓ : ℤ_[ℓ]) ^ eWA ℓ H) • n := by
  intro n hn
  have hK' : (pairOfHom F u₁ h).Kills (B.X ^ ((H + (ℓ - 2)) / (ℓ - 1))) := by
    intro n hn
    obtain ⟨n₁, hn₁, he⟩ := hK n hn
    exact ⟨n₁, hn₁, he⟩
  have hW := (unit_lemma_case_a_level_zero ℓ hℓ A (gbase B u₁ h) D' (pairOfHom F u₁ h) H hv hK').2
  obtain ⟨n₁, hn₁, he⟩ := hW n hn
  refine ⟨n₁, hn₁, ?_⟩
  rw [he, ← IsScalarTower.algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ eWA ℓ H) n, map_pow, map_natCast]

theorem noTors_pow (W : WachMod B M D₀)
    (hZ : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) (k : ℕ) :
    ∀ y, W.QInv y → ((ℓ : ℤ_[ℓ]) ^ k) • y ∈ W.N → y ∈ W.N := by
  induction k with
  | zero =>
    intro y _ hy
    simpa using hy
  | succ k ih =>
    intro y hQ hy
    apply hZ y hQ
    apply ih ((ℓ : ℤ_[ℓ]) • y)
    · rw [← IsScalarTower.algebraMap_smul A (ℓ : ℤ_[ℓ]) y]
      exact W.qInv_smul _ hQ
    · rw [smul_smul, ← pow_succ]
      exact hy

end

theorem lift_exists_first_case : StatLiftA := by
  intro ℓ _ hℓ A _ _ B M u H jumps c hp hPhi hγX hv hc D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S δ
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hδ hQI hφI hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  set eW := eWA ℓ H with heW
  set u₁ : ℤ_[ℓ]ˣ := u ^ (ℓ - 1) with hu₁
  have hu₁c : (u₁ : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ (ℓ - 1) := by rw [hu₁, Units.val_pow_eq_pow_val]
  have hγX₁ : B.GammaX (u₁ : ℤ_[ℓ]) := by rw [hu₁c]; exact hγX
  have hv₁ : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1 := by
    rw [hu₁c, Formalism.ResultantValuation.powSubOneValuation ℓ hℓ (u : ℤ_[ℓ]) hv (ℓ - 1) (by omega),
      Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)),
      add_zero]
  have hCK : CokerKilled S eW := by
    intro n hn
    rw [hp]
    exact homKillsA hℓ S.π u₁ hγX₁ H hv₁ hXK n hn
  have hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE1 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsA hℓ E.S.π u₁ hγX₁ H hv₁ hEK)
  have hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧
      cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE2 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsA hℓ E.S.π u₁ hγX₁ H hv₁ hEK)
  have hRS : RatSurj S :=
    rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁
  set a := M / (ℓ - 1) with ha
  have hMa : M + 1 ≤ (ℓ - 1) * (a + 1) := Nat.lt_mul_div_succ M (by omega)
  have h1 := phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I (ℓ - 1) (a + 1) hPhi hMa hQI hφI
  have hZ := regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hc0 : c 0 = 0 := by
    have := hc 0
    simp only [neg_zero, zpow_zero, Units.val_one, sub_self, mul_eq_zero] at this
    exact this.resolve_left hℓ0
  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], δ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : δ n = x' := by
      have h0 : B.X • (δ n - x') = 0 := by rw [smul_sub, hδ, h, sub_self]
      exact sub_eq_zero.1 (W₀.X_inj _ h0)
    rw [this]; exact hx'
  set R : ℤ_[ℓ][X] := ∏ j ∈ JSet jumps M, (X - C (c j)) with hRdef
  have hR : ∀ y, W₀.QInv y → aeval δ (X * R) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R', hR'⟩ := prod_eig_dvd jumps M (fun j => (X - C (c j)))
    simp only [hc0, map_zero, sub_zero] at hR'
    rw [hRdef, hR', mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_mem _ δ hstab R' _ (hSemi y hy)
  have hprod := prod_sub_one_dvd ℓ hℓ u₁ hv₁ a
  have hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - (u₁ : ℤ_[ℓ]) ^ i)) • y ∈ W₀.N → y ∈ W₀.N := by
    intro y hy h
    obtain ⟨w, hw⟩ := hprod
    apply noTors_pow W₀ hZ _ y hy
    rw [hw, mul_comm, mul_smul]
    exact W₀.smulO_mem w h
  have hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = (u₁ : ℤ_[ℓ]) ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n' := by
    intro i _ _ n hn
    obtain ⟨n', hn', h⟩ := gammaGradedStep_holds ℤ_[ℓ] A B M D₀ W₀ (u₁ : ℤ_[ℓ]) hγX₁ i n hn
    exact ⟨n', hn', by rw [← h]; abel⟩
  have hL0 := lift_wach ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S eW hCK hRS δ R a (ℓ - 1) (u₁ : ℤ_[ℓ]) hPhi
    (by omega) hδ hR (by rw [hp]; exact hZ) hZu hgr h1

  have hcj : ∀ j ∈ JSet jumps M, (0 - c j) ∣ (ℓ : ℤ_[ℓ]) ^ padicValInt ℓ j := by
    intro j hj
    have hj0 : j ≠ 0 := fun h => zero_notMem_JSet jumps M (h ▸ hj)
    obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_ZpowVal ℓ u 1 le_rfl (fun h => absurd h hℓ) hv (-j)
      (neg_ne_zero.2 hj0)
    have hneg : padicValInt ℓ (-j) = padicValInt ℓ j := by simp [padicValInt]
    rw [hneg] at hval
    obtain ⟨w, hw⟩ := dvd_pow_of_val hne hval
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hℓ0
    have e : (ℓ : ℤ_[ℓ]) * ((0 - c j) * w) = (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * w := by
      have := hc j
      linear_combination (-w) * this
    rw [e, ← hw, pow_add, pow_one]
  have hR0 : R.eval 0 ∣ (ℓ : ℤ_[ℓ]) ^ (∑ j ∈ JSet jumps M, padicValInt ℓ j) := by
    rw [hRdef, eval_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    simpa using hcj j hj
  have hfac : a + padicValNat ℓ a.factorial ≤ aStar ℓ M + padicValNat ℓ (aStar ℓ M).factorial := by
    have : padicValNat ℓ (a + 1).factorial = padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial := by
      rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero a) (Nat.factorial_ne_zero _)]
    simp only [aStar, ← ha]
    omega
  have hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + eUA ℓ M (JSet jumps M))) := by
    refine lifts_of_dvd S ?_ hL0
    rw [hp, pow_add]
    apply mul_dvd_mul_left
    simp only [eUA]
    rw [add_assoc, pow_add]
    exact mul_dvd_mul hR0 (dvd_trans hprod (pow_dvd_pow _ hfac))
  intro κ hκ
  obtain ⟨κ₁, hκ₁, h⟩ := finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _
    hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ
  refine ⟨κ₁, hκ₁, ?_⟩
  rw [h, hp, ← pow_add]
  congr 2
  ring

theorem etaleClosed_point_lifts_simple_roots_monic : StatLIFT := ⟨lift_exists_second_case, lift_exists_first_case, lift_to_subgroup_exists⟩

end Formalism.RepresentationBoundsCohomology.N2

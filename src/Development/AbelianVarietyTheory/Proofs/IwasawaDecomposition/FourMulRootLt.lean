module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PowEqOfPartEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC.TameGen

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, ?_⟩
  rw [hz, ← pow_mul, mul_comm, pow_mul]
  have := pow_eq_pow_of_modEq hmod hone
  rwa [pow_one] at this

theorem pow_eq_of_part_eq {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y) :
    ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  refine ⟨a + b, ?_⟩
  have h1 : x ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b)) := by
    rw [pow_add, pow_mul, pow_mul, ha]
  have h2 : y ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b)) := by
    rw [add_comm, pow_add, pow_mul, pow_mul, hb]
  rw [h1, h2, h]

def expo {m : ℕ} : Option (Fin m × Bool) → ℤ
  | none => 0
  | some (j, true) => (j.1 : ℤ) + 1
  | some (j, false) => -((j.1 : ℤ) + 1)

theorem expo_inj {m : ℕ} : Function.Injective (expo (m := m)) := by
  rintro (_ | ⟨i, _ | _⟩) (_ | ⟨j, _ | _⟩) h <;> simp only [expo] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (have : i = j := Fin.ext (by omega); rw [this])

theorem expo_bound {m : ℕ} (o : Option (Fin m × Bool)) : -(m : ℤ) ≤ expo o ∧ expo o ≤ m := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo]
  · omega
  · have := i.2; omega
  · have := i.2; omega

theorem tameList_eq {g m : ℕ} (w : (ZMod g)ˣ) (o : Option (Fin m × Bool)) :
    DC.tameList (fun j : Fin m => w ^ (2 * (j.1 + 1))) o = w ^ (2 * expo o) := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo, DC.tameList]
  · simp
  · rw [mul_neg, zpow_neg, ← zpow_natCast]; push_cast; rfl
  · rw [← zpow_natCast]; push_cast; rfl

theorem dvd_of_pow_eq {g m : ℕ} (w : (ZMod g)ˣ) {o o' : Option (Fin m × Bool)} (hne : o ≠ o') (k : ℕ)
    (h : (w ^ (2 * expo o)) ^ k = (w ^ (2 * expo o')) ^ k) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 4 * m ∧ orderOf w ∣ D * k := by
  have h1 : expo o ≠ expo o' := fun e => hne (expo_inj e)
  have b1 := expo_bound o
  have b2 := expo_bound o'
  refine ⟨(2 * expo o' - 2 * expo o).natAbs, by omega, by omega, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_eq_zpow_iff_modEq] at h
  have h2 := h.dvd
  rw [← sub_mul, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at h2
  exact h2

theorem tameDistinct_gen : ∀ (r g m : ℕ) [Fact g.Prime] (w : (ZMod g)ˣ), orderOf w = g - 1 → 4 * (m : ℝ) * (g : ℝ) ^ ((1 : ℝ) / 4) < (g : ℝ) - 1 → 1 ≤ r → DC.TameDistinct r g (fun j : Fin m => w ^ (2 * (j.1 + 1))) := by
  intro r g m hg w hw hlt hr
  have hg2 : 2 ≤ g := hg.out.two_le
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hq : (1 : ℝ) ≤ (g : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hgR (by norm_num)
  have hm0 : (0 : ℝ) ≤ 4 * (m : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro o o' h
    by_contra hne
    rw [tameList_eq, tameList_eq] at h
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne 1 (by rw [h])
    rw [mul_one, hw] at hdvd
    have h1 : g - 1 ≤ 4 * m := (Nat.le_of_dvd hD0 hdvd).trans hD
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    nlinarith
  · intro l hl hB o o' h
    by_contra hne
    apply hB
    simp only [tameList_eq] at h
    have hfin : ∀ u : (ZMod g)ˣ, IsOfFinOrder (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g)) := by
      intro u
      exact (((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom (ZMod g))).isOfFinOrder
        (isOfFinOrder_of_finite u))
    obtain ⟨a, ha⟩ := pow_eq_of_part_eq hl (hfin _) (hfin _) h
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at ha
    have ha' := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective ha)
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne _ ha'
    rw [hw] at hdvd
    have hn : g - 1 ≠ 0 := by omega
    set v := (g - 1).factorization l with hv
    set M := (g - 1) / l ^ v with hM
    have hmul : l ^ v * M = g - 1 := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
    have hMD : M ∣ D := (Nat.Coprime.pow_right a hcop).dvd_of_dvd_mul_right
      ((Dvd.intro_left _ hmul).trans hdvd)
    have hMle : M ≤ 4 * m := (Nat.le_of_dvd hD0 hMD).trans hD
    have h1 : g - 1 ≤ 4 * m * l ^ v := by
      rw [← hmul, mul_comm]; exact Nat.mul_le_mul_right _ hMle
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m * l ^ v : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    have h3 : (g : ℝ) ^ ((1 : ℝ) / 4) < (l : ℝ) ^ v := lt_of_mul_lt_mul_left (hlt.trans_le h2) hm0
    have h4 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 < ((l : ℝ) ^ v) ^ 4 :=
      pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
    have h5 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = g := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h5, ← pow_mul, mul_comm] at h4
    refine Or.inr ⟨1, le_rfl, hr, hl, ?_⟩
    rw [pow_one, Nat.padicValNat_def, ← Nat.factorization_def _ hl, ← hv]
    exact_mod_cast h4
  · intro j
    exact ⟨w ^ (j.1 + 1), by rw [← pow_add, ← two_mul]⟩

end GlobalTheory.EX.DC.TameGen
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TamePow

theorem four_mul_root_lt {m k g : ℝ} (hm : 2 ≤ m) (hk : m + 3 ≤ k) (hg : k ^ 8 ≤ g) :
    4 * m * g ^ ((1 : ℝ) / 4) < g - 1 := by
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  set t := g ^ ((1 : ℝ) / 4) with ht
  have ht4 : t ^ 4 = g := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hg0]
    norm_num
  have hkt : k ^ 2 ≤ t := by
    have h8 : (k ^ 8) ^ ((1 : ℝ) / 4) ≤ t := Real.rpow_le_rpow (by positivity) hg (by norm_num)
    have e : (k ^ 8) ^ ((1 : ℝ) / 4) = k ^ 2 := by
      rw [show (k ^ 8 : ℝ) = (k ^ 2) ^ (4 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have ht25 : 25 ≤ t := by nlinarith
  have h1 : 4 * m * t < k ^ 2 * t := by
    have : 4 * m < k ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this (by linarith)
  have h2 : k ^ 2 * t ≤ t * t := mul_le_mul_of_nonneg_right hkt (by linarith)
  have hs : 625 ≤ t * t := by nlinarith
  have h3 : t * t + 1 < t ^ 4 := by
    have e4 : t ^ 4 = t * t * (t * t) := by ring
    have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ t * t)
    nlinarith
  linarith

theorem bound_of_over (K : Ctx) (B : Pre) (h : K.Over B) (i : Fin 2) :
    4 * (B.R.m : ℝ) * (B.host.g i : ℝ) ^ ((1 : ℝ) / 4) < (B.host.g i : ℝ) - 1 := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  show 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) < (K.P.H.g i : ℝ) - 1
  have hr : RankVal K.s K.P.R := K.ok.rank
  unfold RankVal at hr
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hr
  have hv : HostVal K.s K.C.P.Cpde K.P.H := K.ok.val
  unfold HostVal at hv
  obtain ⟨-, -, -, -, hg, -⟩ := hv
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have he0 : 0 < K.s.eps := K.s.eps_pos
  have hx0 : (0 : ℝ) ≤ K.s.x := by linarith
  have hd1 : K.s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 : 0 ≤ K.s.delta1 := Real.rpow_nonneg hx0 _
  set y := Real.sqrt K.s.x with hy
  have hy2 : y ^ 2 = K.s.x := Real.sq_sqrt hx0
  have hy1 : 1 ≤ y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1.le
  have hmy : (K.P.R.m : ℝ) ≤ 2 * y := by
    have : Real.sqrt (K.s.x * K.s.delta1) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hk4 : K.s.x ^ (4 : ℕ) ≤ (K.P.R.k : ℝ) := by
    have h1 : K.s.x ^ (4 : ℝ) ≤ K.s.x ^ ((9 : ℝ) / 2 + 10 * K.s.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h2 : K.s.x ^ (4 : ℝ) = K.s.x ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast K.s.x 4
    exact le_trans (le_trans h2.symm.le h1) hk
  have hk8 : y ^ 8 ≤ (K.P.R.k : ℝ) := by
    have : y ^ 8 = K.s.x ^ (4 : ℕ) := by rw [← hy2]; ring
    linarith
  have hk2 : (2 : ℝ) ≤ K.P.R.k := by
    have h1 : (1 : ℝ) < K.P.R.k := lt_of_lt_of_le (one_lt_pow₀ hx1 (by norm_num)) hk4
    have h2 : 1 < K.P.R.k := by exact_mod_cast h1
    exact_mod_cast h2
  have hb : (2.718 : ℝ) ≤ K.s.b := by
    have hL : 1 ≤ K.s.L := Real.one_le_rpow hx1.le he0.le
    have h1 : Real.exp 1 ≤ K.s.b := Real.exp_le_exp.2 hL
    have h2 := Real.exp_one_gt_d9
    linarith
  have hkb1 : (5 : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
  have hkb2 : 2 * y + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have hkb : 2.718 * (K.P.R.k : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
    by_cases h5 : (5 : ℝ) ≤ (K.P.R.k : ℝ)
    · have : y ≤ y ^ 8 := le_self_pow₀ hy1 (by norm_num)
      linarith
    · push_neg at h5
      have hk4' : (K.P.R.k : ℝ) ≤ 4 := by
        have : K.P.R.k < 5 := by exact_mod_cast h5
        have : K.P.R.k ≤ 4 := by omega
        exact_mod_cast this
      have hy12 : y ≤ 1.2 := by
        by_contra hc
        push_neg at hc
        have : (1.2 : ℝ) ^ 8 < y ^ 8 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
        norm_num at this
        linarith
      linarith
  have hM : max 2 (K.P.R.m : ℝ) + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have : max 2 (K.P.R.m : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b - 3 := max_le (by linarith) (by linarith)
    linarith
  have hmain := four_mul_root_lt (le_max_left 2 (K.P.R.m : ℝ)) hM (hg i).1
  have ht : (0 : ℝ) ≤ (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hle : 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) ≤
      4 * max 2 (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := by
    have : (K.P.R.m : ℝ) ≤ max 2 (K.P.R.m : ℝ) := le_max_right _ _
    nlinarith
  linarith

theorem tame_of_pow : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧ ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) → ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩; DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
  have key : ∀ K : Ctx, ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k),
      ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
        ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) →
      ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩;
        DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
    intro K X hO hpow k v
    obtain ⟨w, hw, hchi⟩ := hpow k v
    have hb := bound_of_over K X.B.toPre hO k
    have hr : 1 ≤ X.toD7.R.r := by
      have h2 := X.toD7.R.two_le_m
      first
      | (show 1 ≤ X.toD7.R.k + X.toD7.R.m - 1; omega)
      | omega
      | (simp only [Formalism.MainNotions.Ranks.r]; omega)
      | (unfold Formalism.MainNotions.Ranks.r; omega)
    have e : X.toD7.nd.chiT k v = fun j : Fin X.B.R.m => w ^ (2 * (j.1 + 1)) := funext hchi
    haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩
    have h := GlobalTheory.EX.DC.TameGen.tameDistinct_gen X.toD7.R.r (X.toD7.host.g k) X.B.R.m w hw hb hr
    rw [e]
    exact h
  unfold Ev
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 _ _ _ _
  refine ⟨?k0, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K => ?_⟩⟩⟩⟩
  case k0 => first | exact ⟨0, 0, 0, 0⟩ | exact default | exact Classical.arbitrary _
  first
  | exact key K
  | exact fun _ => key K
  | exact fun _ _ => key K
  | exact fun _ _ _ => key K
  | exact fun _ _ _ _ => key K
  | exact fun _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ _ => key K

end GlobalTheory.Mem.Top.TamePow

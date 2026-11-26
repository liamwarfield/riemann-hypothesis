module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CplFinite

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CorePowMem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LimitPowMem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Imports
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.level :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (J : Ideal A) (u v : A) (b c : Ideal R), Reg2 J u v → b * c ≤ J.map (algebraMap A R) →
      algebraMap A R u ∈ b ⊔ c → algebraMap A R v ∈ b ⊔ c → ∀ l : Module.Dual A R,
        ∃ a : A, ∀ (y : A) (β γ : R), β ∈ b → γ ∈ c → algebraMap A R y = β + γ → l β - y * a ∈ J := by
  intro A R _ _ _ J u v b c hreg hbc hu hv l
  have hl : ∀ x ∈ J.map (algebraMap A R), ∀ r : R, l (r * x) ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact J.mul_mem_right _ hj
    | zero => intro r; simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add (f := _)]; exact J.add_mem (hx r) (hy r)
    | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have key : ∀ (y y' : A) (β γ β' γ' : R), β ∈ b → γ ∈ c → β' ∈ b → γ' ∈ c →
      algebraMap A R y = β + γ → algebraMap A R y' = β' + γ' → y' * l β - y * l β' ∈ J := by
    intro y y' β γ β' γ' hβ hγ hβ' hγ' hy hy'
    have h1 : algebraMap A R y' * β - algebraMap A R y * β' ∈ J.map (algebraMap A R) := by
      apply hbc
      have e : algebraMap A R y' * β - algebraMap A R y * β' = β * γ' - β' * γ := by
        rw [hy, hy']; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_mul hβ hγ') (Ideal.mul_mem_mul hβ' hγ)
    have h2 := hl _ h1 1
    rwa [one_mul, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h2
  obtain ⟨βu, hβu, γu, hγu, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨βv, hβv, γv, hγv, hv'⟩ := Submodule.mem_sup.mp hv
  have k := key u v βu γu βv γv hβu hγu hβv hγv hu'.symm hv'.symm
  have hm : v * l βu ∈ J ⊔ Ideal.span {u} := by
    have e : v * l βu = (v * l βu - u * l βv) + u * l βv := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left k)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨l βv, mul_comm _ _⟩))
  obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp (hreg.2 _ hm)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨a, fun y β γ hβ hγ hy => hreg.1 _ ?_⟩
  have k2 := key y u β γ βu γu hβ hγ hβu hγu hy hu'.symm
  have e : u * (l β - y * a) = (u * l β - y * l βu) + y * j := by
    rw [← hjs]; ring
  rw [e]
  exact J.add_mem k2 (J.mul_mem_left _ hj)
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.limit_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K₀, ∀ K, K₀ ≤ K → x ^ K ∈ b ^ M ⊔ c ^ M := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n * (M + M), fun K hK => ?_⟩
  have h1 : x ^ (n * (M + M)) ∈ b ^ M ⊔ c ^ M := by
    rw [pow_mul]
    exact Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_mem_pow hn _)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [pow_add]
  exact Ideal.mul_mem_right _ _ h1

private theorem smodEq_ideal_pow_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem UpperTheory.V.AlgebraTools.Conn.limit :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c : Ideal R),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) →
      (∀ m, ∃ N, I ^ N ≤ J m) → b * c ≤ (I.map (algebraMap A R)).radical → b.FG → c.FG →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      ∃ a : Module.Dual A (Module.Dual A R), ∀ m, ∃ N, m ≤ N ∧ ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N →
        algebraMap A R y = β + γ → ∀ l : Module.Dual A R, l β - y * a l ∈ I ^ m := by
  intro A R _ _ _ I _ J u v b c hJ hJI hreg hIJ hbc hb hc hu hv
  let P : ℕ → ℕ → Module.Dual A R → A → Prop := fun m N l a =>
    ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N → algebraMap A R y = β + γ → l β - y * a ∈ J m
  have weak : ∀ m m' N N' l a, m ≤ m' → N ≤ N' → P m' N l a → P m N' l a := by
    intro m m' N N' l a hm hN h y β γ hβ hγ hy
    exact hJ hm (h y β γ (Ideal.pow_le_pow_right hN hβ) (Ideal.pow_le_pow_right hN hγ) hy)
  have uniq : ∀ m N l a a', P m N l a → P m N l a' → a - a' ∈ J m := by
    intro m N l a a' h h'
    obtain ⟨K, hK⟩ := limit_pow_mem b c (algebraMap A R u) hu N
    have hmem := hK K le_rfl
    rw [← map_pow] at hmem
    obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp hmem
    have e1 := h (u ^ K) β γ hβ hγ hsum.symm
    have e2 := h' (u ^ K) β γ hβ hγ hsum.symm
    apply (hreg m K).1
    have e3 := Ideal.sub_mem _ e2 e1
    convert e3 using 1
    ring
  have exist : ∀ m, ∃ N, m ≤ N ∧ ∀ l, ∃ a, P m N l a := by
    intro m
    obtain ⟨N₁, hN₁⟩ := hIJ m
    obtain ⟨P₀, hP₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hbc (Submodule.FG.mul hb hc)
    refine ⟨max m (P₀ * N₁), le_max_left _ _, fun l => ?_⟩
    obtain ⟨Ku, hKu⟩ := limit_pow_mem b c (algebraMap A R u) hu (max m (P₀ * N₁))
    obtain ⟨Kv, hKv⟩ := limit_pow_mem b c (algebraMap A R v) hv (max m (P₀ * N₁))
    have hprod : b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) ≤ Ideal.map (algebraMap A R) (J m) := by
      calc b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) = (b * c) ^ (max m (P₀ * N₁)) := (mul_pow b c _).symm
        _ ≤ (b * c) ^ (P₀ * N₁) := Ideal.pow_le_pow_right (le_max_right _ _)
        _ = ((b * c) ^ P₀) ^ N₁ := pow_mul _ _ _
        _ ≤ (I.map (algebraMap A R)) ^ N₁ := Ideal.pow_right_mono hP₀ N₁
        _ = (I ^ N₁).map (algebraMap A R) := (Ideal.map_pow _ _ _).symm
        _ ≤ (J m).map (algebraMap A R) := Ideal.map_mono hN₁
    have hu' : algebraMap A R (u ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁)) := by
      rw [map_pow]
      exact hKu _ (le_max_left _ _)
    have hv' : algebraMap A R (v ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁)) := by
      rw [map_pow]
      exact hKv _ (le_max_right _ _)
    obtain ⟨a, ha⟩ := level (J m) (u ^ (max Ku Kv)) (v ^ (max Ku Kv)) _ _ (hreg m _) hprod hu' hv' l
    exact ⟨a, ha⟩
  choose N hNm hN using exist
  choose a ha using hN
  have hcauchy : ∀ l m n, m ≤ n → a m l - a n l ∈ J m := by
    intro l m n hmn
    apply uniq m (max (N m) (N n)) l
    · exact weak m m (N m) _ l _ le_rfl (le_max_left _ _) (ha m l)
    · exact weak m n (N n) _ l _ hmn (le_max_right _ _) (ha n l)
  have hlim : ∀ l, ∃ L : A, ∀ n, a n l - L ∈ I ^ n := by
    intro l
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := fun n => a n l)
      (fun {m n} hmn => by
        rw [smodEq_ideal_pow_iff_sub_mem]
        exact hJI m (hcauchy l m n hmn))
    exact ⟨L, fun n => (smodEq_ideal_pow_iff_sub_mem I n _ _).mp (hL n)⟩
  choose L hL using hlim
  have haus : ∀ x : A, (∀ n, x ∈ I ^ n) → x = 0 := by
    intro x hx
    apply IsHausdorff.haus (I := I) inferInstance x
    intro n
    rw [smodEq_ideal_pow_iff_sub_mem, sub_zero]
    exact hx n
  have hadd : ∀ m l l', a m (l + l') - a m l - a m l' ∈ J m := by
    intro m l l'
    have h3 : P m (N m) (l + l') (a m l + a m l') := by
      intro y β γ hβ hγ hy
      have e := Ideal.add_mem _ (ha m l y β γ hβ hγ hy) (ha m l' y β γ hβ hγ hy)
      convert e using 1
      simp only [LinearMap.add_apply]
      ring
    have e := uniq m (N m) (l + l') _ _ (ha m (l + l')) h3
    convert e using 1
    ring
  have hsmul : ∀ m (r : A) l, a m (r • l) - r * a m l ∈ J m := by
    intro m r l
    have h3 : P m (N m) (r • l) (r * a m l) := by
      intro y β γ hβ hγ hy
      have e := Ideal.mul_mem_left _ r (ha m l y β γ hβ hγ hy)
      convert e using 1
      simp only [LinearMap.smul_apply, smul_eq_mul]
      ring
    exact uniq m (N m) (r • l) _ _ (ha m (r • l)) h3
  let Φ : Module.Dual A (Module.Dual A R) :=
    { toFun := L
      map_add' := by
        intro l l'
        have h0 := haus (L (l + l') - (L l + L l')) (fun n => by
          have e := Ideal.sub_mem _ (Ideal.sub_mem _ (hL (l + l') n) (hL l n)) (hL l' n)
          have e2 := hJI n (hadd n l l')
          have e3 := Ideal.sub_mem _ e2 e
          convert e3 using 1
          ring)
        exact sub_eq_zero.mp h0
      map_smul' := by
        intro r l
        have h0 := haus (L (r • l) - r * L l) (fun n => by
          have e := Ideal.sub_mem _ (hL (r • l) n) (Ideal.mul_mem_left _ r (hL l n))
          have e2 := hJI n (hsmul n r l)
          have e3 := Ideal.sub_mem _ e2 e
          convert e3 using 1
          ring)
        rw [sub_eq_zero] at h0
        simpa using h0 }
  refine ⟨Φ, fun m => ⟨N m, hNm m, fun y β γ hβ hγ hy l => ?_⟩⟩
  have e1 := hJI m (ha m l y β γ hβ hγ hy)
  have e2 := Ideal.mul_mem_left _ y (hL l m)
  have e3 := Ideal.add_mem _ e1 e2
  show l β - y * L l ∈ I ^ m
  convert e3 using 1
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.FormsAR
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem formsAR_embed {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ (ι : Type) (_ : Fintype ι) (f : M →ₗ[R] (ι → R)), Function.Injective f := by
  classical
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, indepI, hI⟩ := exists_maximal_linearIndepOn R s
  have indepI' : LinearIndependent R (fun x : I => s x) := indepI
  let N := Submodule.span R (Set.range fun x : I => s x)
  let b : Module.Basis I R N := Module.Basis.span indepI'
  have exists_a : ∀ i, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases hi : i ∈ I
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact Submodule.subset_span (Set.mem_range_self (⟨i, hi⟩ : I))
    · obtain ⟨a, ha, ha'⟩ := hI i hi
      refine ⟨a, ha, ?_⟩
      rwa [Set.image_eq_range s I] at ha'
  choose a ha ha' using exists_a
  have hA : (∏ i, a i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => ha i
  let φ : M →ₗ[R] M := LinearMap.lsmul R M (∏ i, a i)
  have hφ : Function.Injective φ := LinearMap.ker_eq_bot.mp (LinearMap.ker_lsmul hA)
  have hle : LinearMap.range φ ≤ N := by
    suffices ∀ i, φ (s i) ∈ N by
      rw [LinearMap.range_eq_map, ← hs, Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      apply this
    intro i
    have h1 := N.smul_mem (∏ j ∈ {i}ᶜ, a j) (ha' i)
    rw [← mul_smul, ← Fintype.prod_eq_prod_compl_mul i] at h1
    exact h1
  refine ⟨I, inferInstance,
    b.equivFun.toLinearMap ∘ₗ φ.codRestrict N (fun x => hle ⟨x, rfl⟩), ?_⟩
  intro x y h
  have h2 := b.equivFun.injective h
  exact hφ (congrArg Subtype.val h2)

private theorem formsAR_pi {R ι : Type} [CommRing R] [Fintype ι] (J : Ideal R) (x : ι → R)
    (hx : ∀ i, x i ∈ J) : x ∈ J • (⊤ : Submodule R (ι → R)) := by
  classical
  have : x = ∑ i, x i • (Pi.single i (1 : R) : ι → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

theorem UpperTheory.V.AlgebraTools.Conn.formsAR :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      [Module.IsTorsionFree A M] (I : Ideal A), ∃ k : ℕ, ∀ (n : ℕ) (m : M),
        (∀ l : Module.Dual A M, l m ∈ I ^ (n + k)) → m ∈ I ^ n • (⊤ : Submodule A M) := by
  intro A M _ _ _ _ _ _ _ I
  obtain ⟨ι, _, f, hf⟩ := formsAR_embed (R := A) (M := M)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun n m hm => ?_⟩
  have h1 : f m ∈ I ^ (n + k) • (⊤ : Submodule A (ι → A)) ⊓ LinearMap.range f :=
    ⟨formsAR_pi _ _ fun i => hm ((LinearMap.proj i) ∘ₗ f), ⟨m, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : f m ∈ I ^ n • LinearMap.range f := Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨y, hy, hym⟩ := h2
  rw [← hf hym]
  exact hy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LatticeDuality
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.bidual :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a : Module.Dual A (Module.Dual A M)), ∃ (d : A) (r : M), d ≠ 0 ∧ ∀ l : Module.Dual A M, l r = d * a l := by
  intro A M _ _ _ _ _ a
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  let K := FractionRing A
  let ψ : Module.Dual A M → Option S → K := fun l o =>
    o.elim (algebraMap A K (a l)) (fun i => algebraMap A K (l (i : M)))
  have hψs : ∀ (p : A) l o, ψ (p • l) o = algebraMap A K p * ψ l o := by
    intro p l o
    cases o <;> simp [ψ]
  have hψa : ∀ l m o, ψ (l + m) o = ψ l o + ψ m o := by
    intro l m o
    cases o <;> simp [ψ]
  have hψ0 : ∀ o, ψ 0 o = 0 := by
    intro o
    cases o <;> simp [ψ]
  let v : Option S → K := fun j => if none = j then 1 else 0
  have key : ∀ w ∈ Submodule.span K (Set.range ψ),
      ∃ s : A, s ≠ 0 ∧ ∃ l, ∀ o, algebraMap A K s * w o = ψ l o := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨1, one_ne_zero, l, fun o => by simp⟩
    | zero =>
      exact ⟨1, one_ne_zero, 0, fun o => by simp [hψ0]⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨t, ht, m, hm⟩ := hy
      refine ⟨s * t, mul_ne_zero hs ht, t • l + s • m, fun o => ?_⟩
      rw [hψa, hψs, hψs, ← hl o, ← hm o, Pi.add_apply, map_mul]
      ring
    | smul c x _ hx =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have hq0 : algebraMap A K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
      have hc : algebraMap A K q * (algebraMap A K p / algebraMap A K q) = algebraMap A K p :=
        mul_div_cancel₀ _ hq0
      refine ⟨q * s, mul_ne_zero (nonZeroDivisors.ne_zero hq) hs, p • l, fun o => ?_⟩
      rw [hψs, ← hl o, Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (algebraMap A K s * x o) * hc
  have hv : v ∉ Submodule.span K (Set.range ψ) := by
    intro hmem
    obtain ⟨s, hs, l, hl⟩ := key v hmem
    have hl0 : l = 0 := by
      apply LinearMap.ext_on hS
      intro i hi
      have h := hl (some ⟨i, hi⟩)
      simp [v, ψ] at h
      rw [LinearMap.zero_apply]
      exact IsFractionRing.injective A K (by rw [map_zero]; exact h.symm)
    subst hl0
    have h := hl none
    simp [v, ψ] at h
    exact hs h
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hf0 : ∀ l, f (ψ l) = 0 := by
    intro l
    have h : f (ψ l) ∈ (Submodule.span K (Set.range ψ)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    rw [hfW] at h
    exact (Submodule.mem_bot K).mp h
  let c : Option S → K := fun o => f (fun j => if o = j then 1 else 0)
  obtain ⟨Dn, hDc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  choose b hb using hDc
  have hD0 : algebraMap A K (Dn : A) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Dn.2
  have hmain : ∀ l : Module.Dual A M, b none * a l + ∑ i : S, b (some i) * l i = 0 := by
    intro l
    have e : ∑ o, ψ l o * c o = 0 := by
      have h := hf0 l
      rw [LinearMap.pi_apply_eq_sum_univ f (ψ l)] at h
      simpa [c, smul_eq_mul] using h
    apply IsFractionRing.injective A K
    rw [map_zero]
    calc algebraMap A K (b none * a l + ∑ i : S, b (some i) * l i)
        = algebraMap A K (Dn : A) * ∑ o, ψ l o * c o := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Fintype.sum_option, mul_add, Finset.mul_sum, map_add (f := _), map_mul, map_sum]
          congr 1
          · rw [hb, Algebra.smul_def]
            simp only [ψ, Option.elim_none]
            ring
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_mul, hb, Algebra.smul_def]
            simp only [ψ, Option.elim_some]
            ring
      _ = 0 := by rw [e, mul_zero]
  refine ⟨b none, -(∑ i : S, b (some i) • (i : M)), ?_, ?_⟩
  · intro h0
    have h := hb none
    rw [h0, map_zero, Algebra.smul_def] at h
    exact hf ((mul_eq_zero.mp h.symm).resolve_left hD0)
  · intro l
    have h := hmain l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_smul, smul_eq_mul]
    linear_combination -h
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.core_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K, x ^ K ∈ b ^ M ⊔ c ^ M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, by simp⟩
  · have hx' : x ∈ (b ^ M ⊔ c ^ M).radical := by
      rw [Ideal.radical_sup, Ideal.radical_pow _ hM.ne', Ideal.radical_pow _ hM.ne',
        ← Ideal.radical_sup]
      exact hx
    exact hx'

private theorem UpperTheory.V.AlgebraTools.Conn.core_krull {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (P : Ideal R) (hP : P.IsPrime) (y r : R) (hy : y ∉ P)
    (h : ∀ n : ℕ, ∃ K : ℕ, y ^ K * r ∈ P ^ n) : r = 0 := by
  haveI := hP
  have hmem : ∀ n : ℕ, algebraMap R (Localization.AtPrime P) r ∈
      (maximalIdeal (Localization.AtPrime P)) ^ n := by
    intro n
    obtain ⟨K, hK⟩ := h n
    have h1 : algebraMap R (Localization.AtPrime P) (y ^ K * r) ∈
        (maximalIdeal (Localization.AtPrime P)) ^ n := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hK
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) (y ^ K)) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨y ^ K, P.primeCompl.pow_mem hy K⟩ : P.primeCompl)
    rw [map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have h0 : algebraMap R (Localization.AtPrime P) r = 0 := by
    have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime P))
      (maximalIdeal.isMaximal _).ne_top
    rw [← Ideal.mem_bot, ← hb, Ideal.mem_iInf]
    exact hmem
  exact IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
    (h0.trans (map_zero _).symm)

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.AlgebraTools.Conn.core :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
      [FaithfulSMul A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c P Q : Ideal R) (y z : A),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) → (∀ m, ∃ N, I ^ N ≤ J m) →
      b * c ≤ (I.map (algebraMap A R)).radical →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      P.IsPrime → Q.IsPrime → b ≤ P → c ≤ Q → I.map (algebraMap A R) ≤ P → I.map (algebraMap A R) ≤ Q →
      algebraMap A R y ∈ (b ⊔ c).radical → algebraMap A R z ∈ (b ⊔ c).radical →
      algebraMap A R y ∉ P → algebraMap A R z ∉ Q → False := by
  intro A R _ _ _ _ _ _ _ _ I _ J u v b c P Q y z hJ hJI hreg hIJ hbc hu hv hP hQ hbP hcQ hIP hIQ
    hy hz hyP hzQ
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  obtain ⟨a, ha⟩ := UpperTheory.V.AlgebraTools.Conn.limit (R := R) I J u v b c hJ hJI hreg hIJ hbc
    (IsNoetherian.noetherian b) (IsNoetherian.noetherian c) hu hv
  obtain ⟨d, r, hd, hr⟩ := UpperTheory.V.AlgebraTools.Conn.bidual (M := R) a
  obtain ⟨k, hk⟩ := UpperTheory.V.AlgebraTools.Conn.formsAR (M := R) I
  have key : ∀ w : A, algebraMap A R w ∈ (b ⊔ c).radical → ∀ n : ℕ, ∃ N, n ≤ N ∧ ∃ K : ℕ,
      ∃ β ∈ b ^ N, ∃ γ ∈ c ^ N, β + γ = (algebraMap A R w) ^ K ∧
      algebraMap A R d * β - (algebraMap A R w) ^ K * r ∈ (I.map (algebraMap A R)) ^ n := by
    intro w hw n
    obtain ⟨N, hnN, hN⟩ := ha (n + k)
    obtain ⟨K, hK⟩ := core_pow_mem b c _ hw N
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hK
    refine ⟨N, le_trans (Nat.le_add_right n k) hnN, K, β, hβ, γ, hγ, hβγ, ?_⟩
    have hforms : ∀ l : Module.Dual A R, l (d • β - w ^ K • r) ∈ I ^ (n + k) := by
      intro l
      have h1 := hN (w ^ K) β γ hβ hγ (by rw [map_pow, hβγ]) l
      have h2 : l (d • β - w ^ K • r) = d * (l β - w ^ K * a l) := by
        rw [map_sub, map_smul, map_smul, hr, smul_eq_mul, smul_eq_mul]
        ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ h1
    have h4 : d • β - w ^ K • r ∈ Ideal.map (algebraMap A R) (I ^ n) := by
      have h3 := hk n _ hforms
      rw [Ideal.smul_top_eq_map] at h3
      exact h3
    rw [← Ideal.map_pow]
    simpa [Algebra.smul_def] using h4
  have hr0 : r = 0 := by
    refine core_krull P hP (algebraMap A R y) r hyP fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, -, hdiff⟩ := key y hy n
    refine ⟨K, ?_⟩
    have hβP : β ∈ P ^ n := Ideal.pow_right_mono hbP n (Ideal.pow_le_pow_right hnN hβ)
    have hd' : algebraMap A R d * β - (algebraMap A R y) ^ K * r ∈ P ^ n :=
      Ideal.pow_right_mono hIP n hdiff
    have he : (algebraMap A R y) ^ K * r =
        algebraMap A R d * β - (algebraMap A R d * β - (algebraMap A R y) ^ K * r) := by ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hβP) hd'
  have hdr : algebraMap A R d - r = 0 := by
    refine core_krull Q hQ (algebraMap A R z) _ hzQ fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, hβγ, hdiff⟩ := key z hz n
    refine ⟨K, ?_⟩
    have hγQ : γ ∈ Q ^ n := Ideal.pow_right_mono hcQ n (Ideal.pow_le_pow_right hnN hγ)
    have hd' : algebraMap A R d * β - (algebraMap A R z) ^ K * r ∈ Q ^ n :=
      Ideal.pow_right_mono hIQ n hdiff
    have he : (algebraMap A R z) ^ K * (algebraMap A R d - r) =
        (algebraMap A R d * β - (algebraMap A R z) ^ K * r) + algebraMap A R d * γ := by
      rw [← hβγ]
      ring
    rw [he]
    exact Ideal.add_mem _ hd' (Ideal.mul_mem_left _ _ hγQ)
  rw [hr0, sub_zero] at hdr
  exact hd (FaithfulSMul.algebraMap_injective A R (hdr.trans (map_zero _).symm))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ExistsSystemOfParameters
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.exists_system_of_parameters {A : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (J : Ideal A) (hle : J ≤ maximalIdeal A) :
    ∃ ys : List A, (∀ y ∈ ys, y ∈ maximalIdeal A) ∧
      (ys.length : WithBot ℕ∞) = ringKrullDim (A ⧸ J) ∧
      ∀ P : Ideal A, P.IsPrime → J ≤ P → (∀ y ∈ ys, y ∈ P) → P = maximalIdeal A := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (A ⧸ J))
  obtain ⟨g, hg⟩ := hsurj.hasRightInverse
  refine ⟨s.toList.map g, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h1 : π (g z) ∈ maximalIdeal (A ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (Finset.mem_toList.1 hz))
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    simp
  · intro P hP hJP hy
    have hker : RingHom.ker π ≤ P := by rw [hπ, Ideal.mk_ker]; exact hJP
    have hP' : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
    have hs' : Ideal.span (s : Set (A ⧸ J)) ≤ P.map π := by
      rw [Ideal.span_le]
      intro z hz
      rw [← hg z]
      exact Ideal.mem_map_of_mem π (hy _ (List.mem_map.2 ⟨z, Finset.mem_toList.2 hz, rfl⟩))
    have hm : maximalIdeal (A ⧸ J) ≤ P.map π :=
      hs.2 ⟨hP', hs'⟩ (le_maximalIdeal hP'.ne_top)
    refine le_antisymm (le_maximalIdeal hP.ne_top) fun a ha => ?_
    have h1 : π a ∈ P.map π := hm (map_nonunit π a ha)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective π hsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.2 hker] at h1
    exact h1

private theorem UpperTheory.V.AlgebraTools.Conn.weakly_regular_mem_of_mul {A : Type} [CommRing A] (l w : List A) (a : A)
    (h : RingTheory.Sequence.IsWeaklyRegular A (l ++ a :: w)) (x : A)
    (hx : a * x ∈ Ideal.ofList l) : x ∈ Ideal.ofList l := by
  have h1 := h.regular_mod_prev l.length (by simp)
  simp only [List.getElem_append_right, le_refl, Nat.sub_self,
    List.getElem_cons_zero] at h1
  rw [List.take_left' rfl] at h1
  have e : (Ideal.ofList l • (⊤ : Submodule A A)) = Ideal.ofList l := by
    rw [smul_eq_mul, Ideal.mul_top]
  have h2 : (Submodule.Quotient.mk x : A ⧸ (Ideal.ofList l • (⊤ : Submodule A A))) = 0 := by
    apply h1
    show a • _ = a • _
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, e]
    exact hx
  rwa [Submodule.Quotient.mk_eq_zero, e] at h2

theorem UpperTheory.V.AlgebraTools.Conn.reg2 :
    ∀ {A : Type} [CommRing A] [IsLocalRing A], ReciprocityTheory.CA.IsCM A → ∀ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A → 2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) →
      ∃ u ∈ maximalIdeal A, ∃ v ∈ maximalIdeal A, ∀ m K : ℕ,
        Reg2 (Ideal.ofList (xs.map (· ^ (m + 1)))) (u ^ K) (v ^ K) := by
  intro A _ _ hA xs hxs hdim h2
  haveI := hA.1
  obtain ⟨ys, hys, hlen, hP⟩ := exists_system_of_parameters (Ideal.ofList xs) (Ideal.span_le.2 hxs)
  rw [← hlen] at hdim h2
  have h2' : 2 ≤ ys.length := by exact_mod_cast h2
  obtain ⟨u, v, w, rfl⟩ : ∃ u v w, ys = u :: v :: w := by
    match ys, h2' with
    | u :: v :: w, _ => exact ⟨u, v, w, rfl⟩
  have hu := hys u (by simp)
  have hv := hys v (by simp)
  refine ⟨u, hu, v, hv, fun m K => ?_⟩
  rcases K with _ | K
  · simpa using isWeaklyRegularPairMod_one_left _ _
  set l := xs.map (· ^ (m + 1)) with hl
  have hreg : RingTheory.Sequence.IsRegular A (l ++ u ^ (K + 1) :: v ^ (K + 1) :: w) := by
    refine hA.isRegular_of_isArtinianRing_quotient _ ?_ ?_ ?_
    · intro r hr
      simp only [hl, List.mem_append, List.mem_map, List.mem_cons] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl | hr
      · exact Ideal.pow_mem_of_mem _ (hxs x hx) _ (Nat.succ_pos _)
      · exact Ideal.pow_mem_of_mem _ hu _ (Nat.succ_pos _)
      · exact Ideal.pow_mem_of_mem _ hv _ (Nat.succ_pos _)
      · exact hys r (by simp [hr])
    · rw [← hdim]
      simp only [hl, List.length_append, List.length_map, List.length_cons]
      push_cast
      rw [add_comm]
    · set I := Ideal.ofList (l ++ u ^ (K + 1) :: v ^ (K + 1) :: w) with hI
      have : Ring.KrullDimLE 0 (A ⧸ I) := by
        rw [Ring.krullDimLE_zero_iff]
        intro Q hQ
        have hp : (Q.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ _
        have hmem : ∀ r ∈ l ++ u ^ (K + 1) :: v ^ (K + 1) :: w,
            r ∈ Q.comap (Ideal.Quotient.mk I) := by
          intro r hr
          have : r ∈ I := Ideal.subset_span hr
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 this]
          exact Q.zero_mem
        have := hP _ hp (Ideal.span_le.2 fun x hx => hp.mem_of_pow_mem (m + 1)
          (hmem _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)))) (by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | rfl | hy
            · exact hp.mem_of_pow_mem (K + 1) (hmem _ (by simp))
            · exact hp.mem_of_pow_mem (K + 1) (hmem _ (by simp))
            · exact hmem _ (by simp [hy]))
        have hmax : (Q.comap (Ideal.Quotient.mk I)).IsMaximal := this ▸ maximalIdeal.isMaximal A
        rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q]
        refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
          hmax).resolve_left ?_
        rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q]
        exact hQ.ne_top
      exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  refine ⟨weakly_regular_mem_of_mul l _ _ hreg.toIsWeaklyRegular, fun a ha => ?_⟩
  have e : Ideal.ofList (l ++ [u ^ (K + 1)]) = Ideal.ofList l ⊔ Ideal.span {u ^ (K + 1)} := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
  rw [← e] at ha ⊢
  exact weakly_regular_mem_of_mul _ w _ (by simpa using hreg.toIsWeaklyRegular) a ha
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem base_exists_prime {R : Type} [CommRing R] (b : Ideal R)
    (h : 0 < ringKrullDim (R ⧸ b)) : ∃ P : Ideal R, P.IsPrime ∧ b ≤ P ∧ ¬ P.IsMaximal := by
  by_contra hc
  push Not at hc
  have hk : Ring.KrullDimLE 0 (R ⧸ b) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    have hs : Function.Surjective (Ideal.Quotient.mk b) := Ideal.Quotient.mk_surjective
    have h1 : (p.comap (Ideal.Quotient.mk b)).IsMaximal := by
      refine hc _ (Ideal.comap_isPrime _ _) ?_
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact p.zero_mem
    have h2 := Ideal.map_eq_top_or_isMaximal_of_surjective _ hs h1
    rw [Ideal.map_comap_of_surjective _ hs] at h2
    exact h2.resolve_left hp.ne_top
  rw [Ring.krullDimLE_iff] at hk
  exact absurd h (not_lt.2 (by simpa using hk))

private theorem base_exists_out {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [Algebra A R] [Module.Finite A R] (P : Ideal R) (hP : P.IsPrime) (hm : ¬ P.IsMaximal) :
    ∃ y ∈ maximalIdeal A, algebraMap A R y ∉ P := by
  by_contra hcon
  push_neg at hcon
  haveI := hP
  have hle : maximalIdeal A ≤ P.comap (algebraMap A R) := fun y hy => hcon y hy
  have hne : P.comap (algebraMap A R) ≠ ⊤ := (Ideal.comap_isPrime (algebraMap A R) P).ne_top
  have heq : P.comap (algebraMap A R) = maximalIdeal A :=
    ((maximalIdeal.isMaximal A).eq_of_le hne hle).symm
  have hmax : (P.comap (algebraMap A R)).IsMaximal := by
    rw [heq]
    exact maximalIdeal.isMaximal A
  exact hm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A R)
    (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P hmax)

private theorem base_ofList_le {A : Type} [CommRing A] {xs : List A} {I : Ideal A}
    (h : ∀ x ∈ xs, x ∈ I) : Ideal.ofList xs ≤ I :=
  Ideal.span_le.2 fun x hx => h x hx

private theorem base_mem_ofList {A : Type} [CommRing A] {xs : List A} {x : A}
    (h : x ∈ xs) : x ∈ Ideal.ofList xs :=
  Ideal.subset_span h

theorem UpperTheory.V.AlgebraTools.Conn.base :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R] [IsAdicComplete (maximalIdeal A) A], ReciprocityTheory.CA.IsCM A → ∀ (xs : List A) (b c : Ideal R),
      (∀ x ∈ xs, x ∈ maximalIdeal A) → ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A →
      2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) →
      (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → (b ⊔ c).radical = maximalIdeal R →
      0 < ringKrullDim (R ⧸ b) → 0 < ringKrullDim (R ⧸ c) → False := by
  intro A R _ _ _ _ _ _ _ _ _ _ hCM xs b c hxs hdim h2 hrad hsup hb hc
  haveI : IsNoetherianRing A := hCM.1
  have hIm : Ideal.ofList xs ≤ maximalIdeal A := base_ofList_le hxs
  have hIne : Ideal.ofList xs ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hIm
  haveI : IsAdicComplete (Ideal.ofList xs) A := cplFinite (A := A) (B := A) (Ideal.ofList xs) hIne
  obtain ⟨u, hu, v, hv, hreg⟩ := reg2 hCM xs hxs hdim h2
  obtain ⟨P, hP, hbP, hPm⟩ := base_exists_prime b hb
  obtain ⟨Q, hQ, hcQ, hQm⟩ := base_exists_prime c hc
  obtain ⟨y, hy, hyP⟩ := base_exists_out (A := A) P hP hPm
  obtain ⟨z, hz, hzQ⟩ := base_exists_out (A := A) Q hQ hQm
  have hcom : (maximalIdeal R).comap (algebraMap A R) = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R)
    exact IsLocalRing.eq_maximalIdeal this
  have hmem : ∀ a ∈ maximalIdeal A, algebraMap A R a ∈ (b ⊔ c).radical := by
    intro a ha
    rw [hsup, ← Ideal.mem_comap, hcom]
    exact ha
  have hmapI : ∀ {X : Ideal R}, X.IsPrime → b ⊓ c ≤ X →
      Ideal.map (algebraMap A R) (Ideal.ofList xs) ≤ X := by
    intro X hX hbc
    calc Ideal.map (algebraMap A R) (Ideal.ofList xs)
        ≤ (Ideal.map (algebraMap A R) (Ideal.ofList xs)).radical := Ideal.le_radical
      _ = (b ⊓ c).radical := hrad.symm
      _ ≤ X.radical := Ideal.radical_mono hbc
      _ = X := hX.radical
  refine core (Ideal.ofList xs) (fun m => Ideal.ofList (xs.map (fun x => x ^ (m + 1)))) u v b c P Q y z
    ?_ ?_ (fun m K => hreg m K) ?_ ?_ (hmem u hu) (hmem v hv) hP hQ hbP hcQ
    (hmapI hP (inf_le_left.trans hbP)) (hmapI hQ (inf_le_right.trans hcQ))
    (hmem y hy) (hmem z hz) hyP hzQ
  · intro m n hmn
    apply base_ofList_le
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
    have he : x ^ (n + 1) = x ^ (n - m) * x ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    exact Ideal.mul_mem_left _ _ (base_mem_ofList (List.mem_map.2 ⟨x, hx, rfl⟩))
  · intro m
    apply base_ofList_le
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (Ideal.pow_mem_pow (base_mem_ofList hx) (m + 1))
  · intro m
    apply Ideal.exists_pow_le_of_le_radical_of_fg
    · apply base_ofList_le
      intro x hx
      exact ⟨m + 1, base_mem_ofList (List.mem_map.2 ⟨x, hx, rfl⟩)⟩
    · classical
      refine ⟨xs.toFinset, ?_⟩
      rw [List.coe_toFinset]
  · exact Ideal.mul_le_inf.trans (Ideal.le_radical.trans hrad.le)

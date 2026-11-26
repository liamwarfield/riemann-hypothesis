module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeDescentUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def consZero (n : ℕ) : (Fin n → R') →ₗ[R'] (Fin (n + 1) → R') where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp



theorem scalar_descent [IsDomain R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hπ : algebraMap R R' ϖ ≠ 0)
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) :
    ∀ (a : ℕ) (x : R'), (∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ x - x) →
      ∃ c : R, (algebraMap R R' ϖ) ^ a ∣ x - algebraMap R R' c := by
  intro a
  induction a with
  | zero => intro x _; exact ⟨0, by simp⟩
  | succ a ih =>
    intro x hx
    obtain ⟨c0, hc0⟩ := hres x fun σ hσ => (dvd_pow_self _ (Nat.succ_ne_zero a)).trans (hx σ hσ)
    obtain ⟨t, ht⟩ := hc0
    have hx' : x = algebraMap R R' c0 + algebraMap R R' ϖ * t := by rw [← ht]; ring
    have ht' : ∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ t - t := by
      intro σ hσ
      have h := hx σ hσ
      have e : σ x - x = algebraMap R R' ϖ * (σ t - t) := by
        rw [hx']; simp only [map_add (f := _), map_mul, AlgEquiv.commutes]; ring
      rw [e, pow_succ'] at h
      exact (mul_dvd_mul_iff_left hπ).mp h
    obtain ⟨c1, hc1⟩ := ih t ht'
    refine ⟨c0 + ϖ * c1, ?_⟩
    have e : x - algebraMap R R' (c0 + ϖ * c1) = algebraMap R R' ϖ * (t - algebraMap R R' c1) := by
      rw [hx']; simp only [map_add (f := _), map_mul]; ring
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hc1

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

theorem main_induction [IsDomain R'] [IsDiscreteValuationRing R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hirr : Irreducible (algebraMap R R' ϖ))
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) (r : ℕ) :
    ∀ (n : ℕ) (N : Submodule R' (Fin n → R')), (∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N) →
      (∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) →
      (∀ v ∈ N, v ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}) ∧
      (∀ u : Fin n → R', (∀ σ ∈ D, (fun i => σ (u i)) - u ∈ N) →
        ∃ a : Fin n → R', (∀ i, a i ∈ Set.range (algebraMap R R')) ∧ u - a ∈ N) := by
  have hπ : algebraMap R R' ϖ ≠ 0 := hirr.ne_zero
  have hfix : ∀ (σ : R' ≃ₐ[R] R') (y : R'), y ∈ Set.range (algebraMap R R') → σ y = y := by
    rintro σ y ⟨c, rfl⟩; exact AlgEquiv.commutes σ c
  intro n
  induction n with
  | zero =>
    intro N _ _
    refine ⟨fun v _ => ?_, fun u _ => ⟨0, fun i => i.elim0, ?_⟩⟩
    · have : v = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · have : u - 0 = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
  | succ n ih =>
    intro N hlat hstab
    set π := algebraMap R R' ϖ with hπdef
    let L := consZero (R' := R') n
    have hLact : ∀ (σ : R' ≃ₐ[R] R') (w : Fin n → R'),
        (fun i => σ (L w i)) = L (fun i => σ (w i)) := by
      intro σ w; funext i
      refine Fin.cases ?_ ?_ i <;> simp [L, consZero]
    let K := N.comap L
    have hKlat : ∀ w : Fin n → R', π ^ r • w ∈ K := fun w => by
      show L (π ^ r • w) ∈ N
      rw [L.map_smul]; exact hlat _
    have hKstab : ∀ σ ∈ D, ∀ w ∈ K, (fun i => σ (w i)) ∈ K := by
      intro σ hσ w hw
      show L _ ∈ N
      rw [← hLact]; exact hstab σ hσ _ hw
    obtain ⟨hPK, hQK⟩ := ih K hKlat hKstab
    let I : Ideal R' := N.map (LinearMap.proj (R := R') (φ := fun _ : Fin (n + 1) => R') 0)
    have hrI : π ^ r ∈ I := ⟨π ^ r • (fun _ => 1 : Fin (n + 1) → R'), hlat _, by simp⟩
    have hI0 : I ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hrI
      exact pow_ne_zero r hπ hrI
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hirr
    have hmemI : ∀ v ∈ N, π ^ a ∣ v 0 := by
      intro v hv
      have : v 0 ∈ I := ⟨v, hv, rfl⟩
      rw [ha, Ideal.mem_span_singleton] at this
      exact this
    obtain ⟨vs, hvsN, hvs0⟩ : ∃ v ∈ N, v 0 = π ^ a := by
      have : π ^ a ∈ I := by rw [ha]; exact Ideal.subset_span rfl
      obtain ⟨v, hv, hv0⟩ := this
      exact ⟨v, hv, hv0⟩
    have hpa : π ^ a ∈ Set.range (algebraMap R R') := ⟨ϖ ^ a, by simp [hπdef]⟩

    have hvsK : ∀ σ ∈ D, (fun i => σ (Fin.tail vs i)) - Fin.tail vs ∈ K := by
      intro σ hσ
      have e : L ((fun i => σ (Fin.tail vs i)) - Fin.tail vs) = (fun i => σ (vs i)) - vs := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, consZero, hvs0, hfix σ _ hpa]
        · intro j; simp [L, consZero, Fin.tail]
      show L _ ∈ N
      rw [e]; exact N.sub_mem (hstab σ hσ _ hvsN) hvsN
    obtain ⟨a0, ha0, ha0K⟩ := hQK (Fin.tail vs) hvsK
    obtain ⟨vo, hvo⟩ : ∃ vo, vo = vs - L (Fin.tail vs - a0) := ⟨_, rfl⟩
    have hvoN : vo ∈ N := hvo ▸ N.sub_mem hvsN ha0K
    have hvo0 : vo 0 = π ^ a := by rw [hvo]; simp [L, consZero, hvs0]
    have hvorat : ∀ i, vo i ∈ Set.range (algebraMap R R') := by
      intro i
      refine Fin.cases ?_ ?_ i
      · rw [hvo0]; exact hpa
      · intro j
        have : vo j.succ = a0 j := by rw [hvo]; simp [L, consZero, Fin.tail]
        rw [this]; exact ha0 j
    have hrat_add : ∀ x y : R', x ∈ Set.range (algebraMap R R') → y ∈ Set.range (algebraMap R R') →
        x + y ∈ Set.range (algebraMap R R') := by
      rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, map_add _ _ _⟩
    have hrat0 : (0 : R') ∈ Set.range (algebraMap R R') := ⟨0, map_zero _⟩
    have hLrat : ∀ w : Fin n → R', (∀ i, w i ∈ Set.range (algebraMap R R')) →
        ∀ i, L w i ∈ Set.range (algebraMap R R') := by
      intro w hw i
      refine Fin.cases ?_ ?_ i
      · simpa [L, consZero] using hrat0
      · intro j; simpa [L, consZero] using hw j
    refine ⟨?_, ?_⟩
    ·
      intro v hv
      obtain ⟨t, ht⟩ := hmemI v hv
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail (v - t • vo) := ⟨_, rfl⟩
      have hLw : L w = v - t • vo := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, consZero, ht, hvo0]; ring
        · intro j; simp [L, consZero, hw, Fin.tail]
      have hwK : w ∈ K := by
        show L w ∈ N
        rw [hLw]; exact N.sub_mem hv (N.smul_mem t hvoN)
      have hspan : Submodule.span R' {v | v ∈ K ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} ≤
          (Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}).comap L := by
        rw [Submodule.span_le]
        rintro w' ⟨hw'K, hw'r⟩
        exact Submodule.subset_span ⟨hw'K, hLrat w' hw'r⟩
      have h1 : L w ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        hspan (hPK w hwK)
      have h2 : t • vo ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        Submodule.smul_mem _ t (Submodule.subset_span ⟨hvoN, hvorat⟩)
      have : v = L w + t • vo := by rw [hLw]; abel
      rw [this]; exact Submodule.add_mem _ h1 h2
    ·
      intro u hu
      have h0 : ∀ σ ∈ D, π ^ a ∣ σ (u 0) - u 0 := by
        intro σ hσ; simpa using hmemI _ (hu σ hσ)
      obtain ⟨c, hc⟩ := scalar_descent D ϖ hπ hres a (u 0) h0
      obtain ⟨t, ht⟩ := hc
      obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → R', e = Fin.cons (algebraMap R R' c) 0 := ⟨_, rfl⟩
      have herat : ∀ i, e i ∈ Set.range (algebraMap R R') := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [he]; exact ⟨c, rfl⟩
        · intro j; rw [he]; simpa using hrat0
      obtain ⟨u', hu'⟩ : ∃ u', u' = u - e - t • vo := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail u' := ⟨_, rfl⟩
      have hLw : L w = u' := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, consZero, hu', he, hvo0]; rw [ht, hπdef]; ring
        · intro j; simp [L, consZero, hw, Fin.tail]
      have hwinv : ∀ σ ∈ D, (fun i => σ (w i)) - w ∈ K := by
        intro σ hσ
        have key : L ((fun i => σ (w i)) - w) = ((fun i => σ (u i)) - u) - (σ t - t) • vo := by
          rw [L.map_sub, ← hLact, hLw, hu']
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
            hfix σ _ (herat i), hfix σ _ (hvorat i)]
          ring
        show L _ ∈ N
        rw [key]; exact N.sub_mem (hu σ hσ) (N.smul_mem _ hvoN)
      obtain ⟨a', ha', ha'K⟩ := hQK w hwinv
      refine ⟨e + L a', fun i => hrat_add _ _ (herat i) (hLrat a' ha' i), ?_⟩
      have : u - (e + L a') = t • vo + L (w - a') := by
        rw [L.map_sub, hLw, hu']; abel
      rw [this]; exact N.add_mem (N.smul_mem t hvoN) ha'K

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory

theorem stable_lattice_descent_unramified (R R' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    (D : Set (R' ≃ₐ[R] R'))
    (hres : ∀ x : R', (∀ σ ∈ D, σ x - x ∈ maximalIdeal R') →
      ∃ r : R, x - algebraMap R R' r ∈ maximalIdeal R')
    (n r : ℕ) (N : Submodule R' (Fin n → R'))
    (hlat : (maximalIdeal R') ^ r • (⊤ : Submodule R' (Fin n → R')) ≤ N)
    (hstab : ∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) :
    N = Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R R' ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hres' : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c := by
    intro x hx
    obtain ⟨c, hc⟩ := hres x fun σ hσ => by
      rw [hmax, Ideal.mem_span_singleton]; exact hx σ hσ
    rw [hmax, Ideal.mem_span_singleton] at hc
    exact ⟨c, hc⟩
  have hmem : algebraMap R R' ϖ ∈ maximalIdeal R' := by
    rw [hmax]; exact Ideal.mem_span_singleton_self _
  have hlat' : ∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N := fun w =>
    hlat (Submodule.smul_mem_smul (Ideal.pow_mem_pow hmem r) Submodule.mem_top)
  obtain ⟨hP, -⟩ :=
    StableLatticeDescent.main_induction D ϖ hirr hres' r n N hlat' hstab
  exact le_antisymm (fun v hv => hP v hv) (Submodule.span_le.mpr fun v hv => hv.1)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatrixDescent

theorem exists_restrict (R K W K' : Type) [CommRing R] [Field K] [Algebra R K] [CommRing W]
    [Field K'] [Algebra W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K']
    [IsScalarTower R K K'] (hinj : Function.Injective (algebraMap W K')) (σ : K' ≃ₐ[K] K')
    (h1 : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y)
    (h2 : ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) :
    ∃ τ : W ≃ₐ[R] W, ∀ x : W, algebraMap W K' (τ x) = σ (algebraMap W K' x) := by
  choose f hf using h1
  choose f' hf' using h2
  have hl : Function.LeftInverse f' f := by
    intro x; apply hinj; rw [← hf', ← hf]; simp
  have hr : Function.RightInverse f' f := by
    intro x; apply hinj; rw [← hf, ← hf']; simp
  have hm : ∀ x y, f (x * y) = f x * f y := by
    intro x y; apply hinj; rw [map_mul, ← hf, ← hf, ← hf, map_mul, map_mul]
  have ha : ∀ x y, f (x + y) = f x + f y := by
    intro x y; apply hinj; rw [map_add (f := _), ← hf, ← hf, ← hf, map_add (f := _), map_add (f := _)]
  have hc : ∀ r : R, f (algebraMap R W r) = algebraMap R W r := by
    intro r; apply hinj; rw [← hf, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K K', AlgEquiv.commutes]
  let τ : W ≃ₐ[R] W :=
    { toFun := f
      invFun := f'
      left_inv := hl
      right_inv := hr
      map_mul' := hm
      map_add' := ha
      commutes' := hc }
  exact ⟨τ, fun x => (hf x).symm⟩

theorem vecMul_mem_span {W : Type} [CommRing W] {n : ℕ} (g : Matrix (Fin n) (Fin n) W)
    (v : Fin n → W) : Matrix.vecMul v g ∈ Submodule.span W (Set.range g) := by
  have : Matrix.vecMul v g ∈ LinearMap.range g.vecMulLinear := ⟨v, rfl⟩
  rw [range_vecMulLinear] at this
  exact this

theorem mem_span_iff_vecMul {W : Type} [CommRing W] {n : ℕ} (g : Matrix (Fin n) (Fin n) W)
    (v : Fin n → W) : v ∈ Submodule.span W (Set.range g) ↔ ∃ a, Matrix.vecMul a g = v := by
  constructor
  · intro hv
    have : v ∈ LinearMap.range g.vecMulLinear := by rw [range_vecMulLinear]; exact hv
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩; exact vecMul_mem_span g a

theorem rational_rows (R W : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing W] [IsDomain W] [Algebra R W] (hinj : Function.Injective (algebraMap R W))
    (n : ℕ) (g : Matrix (Fin n) (Fin n) W) (hg : g.det ≠ 0) (d : R) (hd : d ≠ 0)
    (hdN : ∀ w : Fin n → W, algebraMap R W d • w ∈ Submodule.span W (Set.range g))
    (hspan : Submodule.span W (Set.range g) = Submodule.span W
      {v | v ∈ Submodule.span W (Set.range g) ∧ ∀ i, v i ∈ Set.range (algebraMap R W)}) :
    ∃ (A : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin n) (Fin n) W),
      IsUnit h.det ∧ A.map (algebraMap R W) = h * g := by
  classical
  set N := Submodule.span W (Set.range g) with hNdef
  let φ : (Fin n → R) →ₗ[R] (Fin n → W) :=
    { toFun := fun a i => algebraMap R W (a i)
      map_add' := by intro a b; funext i; simp
      map_smul' := by intro c a; funext i; simp [Algebra.smul_def] }
  have hφ : ∀ a i, φ a i = algebraMap R W (a i) := fun _ _ => rfl

  let N₀ : Submodule R (Fin n → R) := (N.restrictScalars R).comap φ
  have hdN₀ : ∀ a : Fin n → R, d • a ∈ N₀ := by
    intro a
    show φ (d • a) ∈ N
    rw [map_smul, ← algebraMap_smul W d (φ a)]
    exact hdN _
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) N₀
  have hmn : m = n := by
    have e : Module.finrank R N₀ = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    apply le_antisymm
    · rw [← e]
      exact (Submodule.finrank_le N₀).trans (Module.finrank_fin_fun R).le
    · haveI : Module.Finite R N₀ := Module.Finite.of_basis b
      let ψ : (Fin n → R) →ₗ[R] N₀ := (d • LinearMap.id).codRestrict N₀ hdN₀
      have hψ : Function.Injective ψ := by
        intro a a' haa
        have := congrArg Subtype.val haa
        exact smul_right_injective (Fin n → R) hd this
      have := LinearMap.finrank_le_finrank_of_injective hψ
      rwa [Module.finrank_fin_fun, e] at this
  let b' : Module.Basis (Fin n) R N₀ := b.reindex (finCongr hmn)
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i => (b' i : Fin n → R)
  set B := A.map (algebraMap R W) with hBdef
  have hBφ : ∀ i, B i = φ (b' i) := fun i => rfl
  have hBN : ∀ i, B i ∈ N := fun i => (b' i).2
  choose h₀ hh using fun i => (mem_span_iff_vecMul g (B i)).mp (hBN i)
  set h : Matrix (Fin n) (Fin n) W := Matrix.of h₀ with hhdef
  have hAh : A.map (algebraMap R W) = h * g := by
    ext i j
    rw [← hBdef, ← hh i]
    simp [hhdef, Matrix.mul_apply, Matrix.vecMul, dotProduct]

  have hN₀B : ∀ x : N₀, φ x ∈ Submodule.span W (Set.range B) := by
    intro x
    have hx := congrArg Subtype.val (b'.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hx, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul, map_smul, ← hBφ]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hNB : N ≤ Submodule.span W (Set.range B) := by
    rw [hspan, Submodule.span_le]
    rintro v ⟨hvN, hvR⟩
    choose a ha using hvR
    have hva : v = φ a := by funext i; rw [hφ, ha]
    have haN : a ∈ N₀ := by show φ a ∈ N; rw [← hva]; exact hvN
    rw [hva]
    exact hN₀B ⟨a, haN⟩
  choose h₁ hh' using fun i => (mem_span_iff_vecMul B (g i)).mp
    (hNB (Submodule.subset_span ⟨i, rfl⟩))
  set h' : Matrix (Fin n) (Fin n) W := Matrix.of h₁ with hh'def
  have hgB : h' * B = g := by
    ext i j
    rw [← hh' i]
    simp [hh'def, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hinv : h' * h = 1 := by
    have e : (h' * h) * g = g := by rw [Matrix.mul_assoc, ← hAh, ← hBdef, hgB]
    have e2 : g.det • (h' * h - 1) = 0 := by
      have : (h' * h - 1) * (g * g.adjugate) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.sub_mul, e, Matrix.one_mul, sub_self, Matrix.zero_mul]
      rwa [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
    exact sub_eq_zero.mp ((smul_eq_zero.mp e2).resolve_left hg)
  exact ⟨A, h, Matrix.isUnit_det_of_left_inverse hinv, hAh⟩

end GlobalTheory.MatrixDescent

namespace GlobalTheory


open GlobalTheory.MatrixDescent in
theorem matrix_descent_unramified (R K W K' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W]
    [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K']
    [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K']
    (hm : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) (D : Set (K' ≃ₐ[K] K'))
    (hD1 : ∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y)
    (hD2 : ∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y)
    (hres : ∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y →
      y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K') (hg : IsUnit g.det)
    (hstab : ∀ σ ∈ D, ∃ h : Matrix (Fin n) (Fin n) W, g.map σ = h.map (algebraMap W K') * g) :
    ∃ (h : Matrix (Fin n) (Fin n) W) (k : Matrix (Fin n) (Fin n) K),
      IsUnit h.det ∧ k.map (algebraMap K K') = h.map (algebraMap W K') * g := by
  set iW := algebraMap W K' with hiW
  have hinjW : Function.Injective iW := IsFractionRing.injective W K'
  have hRK' : ∀ r : R, algebraMap R K' r = iW (algebraMap R W r) := fun r =>
    IsScalarTower.algebraMap_apply R W K' r
  have hRK'' : ∀ r : R, algebraMap R K' r = algebraMap K K' (algebraMap R K r) := fun r =>
    IsScalarTower.algebraMap_apply R K K' r
  have hinjR : Function.Injective (algebraMap R W) := by
    intro a b hab
    have h1 : algebraMap R K' a = algebraMap R K' b := by rw [hRK', hRK', hab]
    rw [hRK'', hRK''] at h1
    exact IsFractionRing.injective R K ((algebraMap K K').injective h1)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal W = Ideal.span {algebraMap R W ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R W ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors W)
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => g p.1 p.2)
  have hb0 : (b : W) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr
  set c : R := ϖ ^ k with hcdef
  have hc0 : c ≠ 0 := pow_ne_zero k hϖ.ne_zero
  have hcW : algebraMap R W c = (b : W) * u := by rw [hu, hcdef, map_pow]
  have hex : ∀ i j, ∃ w : W, iW w = algebraMap R K' c * g i j := by
    intro i j
    obtain ⟨w, hw⟩ := hb (i, j) (Finset.mem_univ _)
    refine ⟨u * w, ?_⟩
    rw [map_mul, hw, hRK', hcW, Algebra.smul_def, map_mul]
    ring
  choose g' hg' using hex
  have hcK'0 : algebraMap R K' c ≠ 0 := by
    rw [hRK']; exact fun h => hc0 (hinjR (hinjW (by rw [h, map_zero, map_zero])))
  have hdet' : (Matrix.of g').det ≠ 0 := by
    intro h0
    have : iW (Matrix.of g').det = (algebraMap R K' c) ^ n * g.det := by
      rw [RingHom.map_det]
      have e : iW.mapMatrix (Matrix.of g') = algebraMap R K' c • g := by
        ext i j; simp [hg']
      rw [e, Matrix.det_smul, Fintype.card_fin]
    rw [h0, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero n hcK'0) hg.ne_zero) this.symm
  set G : Matrix (Fin n) (Fin n) W := Matrix.of g' with hGdef
  have hGmap : ∀ i j, iW (G i j) = algebraMap R K' c * g i j := fun i j => hg' i j
  set N := Submodule.span W (Set.range G) with hNdef

  obtain ⟨r, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hdet' hirr
  have hdN : ∀ w : Fin n → W, algebraMap R W (ϖ ^ r) • w ∈ N := by
    intro w
    have e : algebraMap R W (ϖ ^ r) • w = Matrix.vecMul ((v : W) • Matrix.vecMul w G.adjugate) G := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul,
        Matrix.vecMul_one, smul_smul, map_pow, ← hv, mul_comm]
    rw [e]; exact vecMul_mem_span G _
  have hlat : (maximalIdeal W) ^ r • (⊤ : Submodule W (Fin n → W)) ≤ N := by
    rw [Submodule.smul_le]
    intro x hx w _
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [mul_smul, ← map_pow]
    exact hdN _

  have hτ : ∀ σ ∈ D, ∃ τ : W ≃ₐ[R] W, ∀ x : W, iW (τ x) = σ (iW x) := fun σ hσ =>
    exists_restrict R K W K' hinjW σ (hD1 σ hσ) (hD2 σ hσ)
  set D' : Set (W ≃ₐ[R] W) := {τ | ∃ σ ∈ D, ∀ x : W, iW (τ x) = σ (iW x)} with hD'def
  have hres' : ∀ x : W, (∀ τ ∈ D', τ x - x ∈ maximalIdeal W) →
      ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W := by
    intro x hx
    apply hres x
    intro σ hσ y hy
    obtain ⟨τ, hτσ⟩ := hτ σ hσ
    have : τ x = y := hinjW (by rw [hτσ, hy])
    rw [← this]; exact hx τ ⟨σ, hσ, hτσ⟩
  have hstab' : ∀ τ ∈ D', ∀ w ∈ N, (fun i => τ (w i)) ∈ N := by
    rintro τ ⟨σ, hσ, hτσ⟩ w hw
    obtain ⟨h, hh⟩ := hstab σ hσ
    have hGτ : G.map τ = h * G := by
      ext i j
      apply hinjW
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, hτσ, hGmap, map_mul, Matrix.mul_apply, map_sum]
      have := congrFun (congrFun hh i) j
      rw [Matrix.map_apply, Matrix.mul_apply] at this
      rw [this, hRK'', AlgEquiv.commutes, ← hRK'', Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hGmap, Matrix.map_apply]; ring
    obtain ⟨a, rfl⟩ := (mem_span_iff_vecMul G w).mp hw
    have e : (fun i => τ (Matrix.vecMul a G i)) =
        Matrix.vecMul (Matrix.vecMul (fun i => τ (a i)) h) G := by
      rw [Matrix.vecMul_vecMul, ← hGτ]
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.vecMul, dotProduct, map_sum]
    rw [e]; exact vecMul_mem_span G _
  have hspan := stable_lattice_descent_unramified R W hm D' hres' n r N hlat hstab'
  obtain ⟨A, h, hhu, hA⟩ :=
    rational_rows R W hinjR n G hdet' (ϖ ^ r) (pow_ne_zero r hϖ.ne_zero) hdN hspan
  refine ⟨h, (algebraMap R K c)⁻¹ • A.map (algebraMap R K), hhu, ?_⟩
  ext i j
  have e1 := congrFun (congrFun hA i) j
  rw [Matrix.map_apply, Matrix.mul_apply] at e1
  have e2 : algebraMap R K' (A i j) = algebraMap R K' c * (h.map iW * g) i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hRK', e1, map_sum, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hGmap, Matrix.map_apply]; ring
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀,
    ← hRK'', ← hRK'', e2]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_descent_unramified_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K'), IsUnit g.det → (∀ σ ∈ D, ∃ h : Matrix (Fin n) (Fin n) W, g.map σ = h.map (algebraMap W K') * g) → ∃ (h : Matrix (Fin n) (Fin n) W) (k : Matrix (Fin n) (Fin n) K), IsUnit h.det ∧ k.map (algebraMap K K') = h.map (algebraMap W K') * g := by
  first | exact @GlobalTheory.matrix_descent_unramified | exact GlobalTheory.matrix_descent_unramified | (intros; apply GlobalTheory.matrix_descent_unramified <;> assumption)
end

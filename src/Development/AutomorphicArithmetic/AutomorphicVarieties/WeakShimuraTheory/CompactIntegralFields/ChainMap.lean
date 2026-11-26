module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainMap
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}

private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

private theorem map_inj (hj : Function.Injective j) {X Y : M4 R} : X.map j = Y.map j ↔ X = Y :=
  (Matrix.map_injective hj).eq_iff

private theorem isGSp_iff (hj : Function.Injective j) (ν : R) (X : M4 R) : IsGSp (j ν) (X.map j) ↔ IsGSp ν X := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp
  rw [adj_map, ← Matrix.map_mul, h, map_inj hj]

private theorem one_iff (hj : Function.Injective j) (X : M4 R) : X.map j = 1 ↔ X = 1 := by
  rw [← Matrix.map_one (⇑j) (map_zero j) (map_one j), map_inj hj]

private theorem diag_iff (hj : Function.Injective j) (X : M4 R) : (X.map j).IsDiag ↔ X.IsDiag := by
  simp only [Matrix.IsDiag, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem up_iff (hj : Function.Injective j) (X : M4 R) : IsUp (X.map j) ↔ IsUp X := by
  simp only [IsUp, Matrix.map_apply, map_eq_zero_iff j hj]

private theorem low_iff (hj : Function.Injective j) (X : M4 R) : IsLow (X.map j) ↔ IsLow X := by
  have h := isGSp_iff hj 1 X
  rw [map_one] at h
  simp only [IsLow, h, Matrix.map_apply, map_eq_zero_iff j hj, map_eq_one_iff j hj]

private theorem suppM_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (X : M4 R) :
    SuppM S (X.map j) ↔ SuppM S X := by
  simp only [SuppM, Matrix.map_apply, map_eq_zero_iff j hj]

variable {ι Γ : Type} [Group Γ]

private theorem r_map (j : R →+* R') (c : PD ι Γ R) (g : Γ) : (c.map j).r g = (c.r g).map j := rfl

private theorem n_map (j : R →+* R') (c : PD ι Γ R) (v : ι) : (c.map j).n v = (c.n v).map j := rfl

private theorem psi_map (j : R →+* R') (c : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (c.map j).ψ v i s = j (c.ψ v i s) := by
  simp only [PD.ψ, r_map, n_map, conj_map, Matrix.map_apply]

private theorem supp_iff (hj : Function.Injective j) (S : Finset (ℤ × ℤ)) (c : PD ι Γ R) :
    Supp S (c.map j).r ↔ Supp S c.r := by
  simp only [Supp, r_map, suppM_iff hj]

private theorem ent_iff (hj : Function.Injective j) (c : PD ι Γ R) (w : ℤ × ℤ) :
    Ent (c.map j).r w ↔ Ent c.r w := by
  simp only [Ent, r_map, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]

private theorem adic_bot {X : Type} [TopologicalSpace X] (f : X → R) : AdicCont ⊥ f ↔ IsLocallyConstant f := by
  refine ⟨fun h => ?_, fun h N => h.comp _⟩
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

private theorem cont_iff [TopologicalSpace Γ] (hj : Function.Injective j) (c : PD ι Γ R) :
    (c.map j).Cont ⊥ ↔ c.Cont ⊥ := by
  simp only [PD.Cont, adic_bot, r_map, Matrix.map_apply]
  exact forall_congr' fun a => forall_congr' fun b =>
    ⟨fun h => IsLocallyConstant.desc _ j h hj, fun h => h.comp j⟩

end

theorem UpperTheory.V.Ws.chainMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k k' : Type} [Field k] [Field k'] (a : O →+* k) (j : k →+* k') (c : PD Φ.ι Γ k),
      (Φ.IsRes (j.comp a) (c.map j) ↔ Φ.IsRes a c) ∧ (Φ.Good (j.comp a) (c.map j) ↔ Φ.Good a c) ∧ Function.Injective fun c : PD Φ.ι Γ k => c.map j := by
  intro O Γ _ _ _ _ _ _ Φ k k' _ _ a j c
  have hj : Function.Injective j := j.injective
  have e1 : ∀ g, IsGSp ((j.comp a) (Φ.ν g : O)) ((c.map j).r g) ↔ IsGSp (a (Φ.ν g)) (c.r g) :=
    fun g => by rw [RingHom.comp_apply, r_map, isGSp_iff hj]
  have e2 : ∀ g, (c.map j).r g = 1 ↔ c.r g = 1 := fun g => by rw [r_map, one_iff hj]
  have e3 : Matrix.IsDiag ((c.map j).r Φ.g0) ↔ Matrix.IsDiag (c.r Φ.g0) := by rw [r_map, diag_iff hj]
  have e4 : ∀ v, IsLow ((c.map j).n v) ↔ IsLow (c.n v) := fun v => by rw [n_map, low_iff hj]
  have e5 : ∀ v s, IsUp (adj ((c.map j).n v) * (c.map j).r s * (c.map j).n v) ↔
      IsUp (adj (c.n v) * c.r s * c.n v) :=
    fun v s => by rw [n_map, r_map, conj_map, up_iff hj]
  have e6 : ∀ v i s, (c.map j).ψ v i s = 1 ↔ c.ψ v i s = 1 :=
    fun v i s => by rw [psi_map, map_eq_one_iff j hj]
  have e7 : ∀ g i, (c.map j).r g i i = (j.comp a) (Φ.χ i g : O) ↔ c.r g i i = a (Φ.χ i g) :=
    fun g i => by rw [r_map, Matrix.map_apply, RingHom.comp_apply, hj.eq_iff]
  have e8 : ∀ v i s, (c.map j).ψ v i s = (j.comp a) (Φ.χ i s : O) ↔ c.ψ v i s = a (Φ.χ i s) :=
    fun v i s => by rw [psi_map, RingHom.comp_apply, hj.eq_iff]
  have e9 : ((Supp nP (c.map j).r ∧ ∀ v, SuppM qQ ((c.map j).n v)) ∨ Supp nM (c.map j).r) ↔
      ((Supp nP c.r ∧ ∀ v, SuppM qQ (c.n v)) ∨ Supp nM c.r) := by
    simp only [supp_iff hj, n_map, suppM_iff hj]
  have e10 : Fr.InV (Φ := Φ) (c.map j) ↔ Fr.InV (Φ := Φ) c := by
    simp only [Fr.InV, supp_iff hj, n_map, suppM_iff hj, Matrix.map_apply, ne_eq, map_eq_zero_iff j hj]
  have hP : Φ.IsPair (j.comp a) (c.map j) ↔ Φ.IsPair a c :=
    ⟨fun h => ⟨fun g => (e1 g).1 (h.mult g), fun g hg => (e2 g).1 (h.kill g hg), e3.1 h.nrm,
        fun v => (e4 v).1 (h.low v), fun v s hs => (e5 v s).1 (h.flag v s hs),
        fun v s hs i => (e6 v i s).1 (h.mu v s hs i)⟩,
      fun h => ⟨fun g => (e1 g).2 (h.mult g), fun g hg => (e2 g).2 (h.kill g hg), e3.2 h.nrm,
        fun v => (e4 v).2 (h.low v), fun v s hs => (e5 v s).2 (h.flag v s hs),
        fun v s hs i => (e6 v i s).2 (h.mu v s hs i)⟩⟩
  have hR : Φ.Res (j.comp a) (c.map j) ↔ Φ.Res a c :=
    ⟨fun h => ⟨fun g i => (e7 g i).1 (h.diag g i), fun v s hs i => (e8 v i s).1 (h.char v s hs i),
        e9.1 h.shape⟩,
      fun h => ⟨fun g i => (e7 g i).2 (h.diag g i), fun v s hs i => (e8 v i s).2 (h.char v s hs i),
        e9.2 h.shape⟩⟩
  refine ⟨⟨fun h => ⟨hP.1 h.pair, hR.1 h.res, (cont_iff hj c).1 h.cont⟩,
    fun h => ⟨hP.2 h.pair, hR.2 h.res, (cont_iff hj c).2 h.cont⟩⟩, ?_, ?_⟩
  · simp only [Fr.Good, ent_iff hj, e10, RingHom.comp_apply, ne_eq, map_eq_one_iff j hj]
  · intro x y h
    apply PD.ext
    · ext g : 1
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.r g) h)
    · funext v
      exact (map_inj hj).1 (congrArg (fun e : PD Φ.ι Γ k' => e.n v) h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GlobalTheory
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.LineM

variable {k : Type} [Field k]

private def GlobalTheory (X : M4 k) : Prop := ∀ i j : Fin 4, (i.1 < 2 ∨ 2 ≤ j.1) → X i j = 0

private def Par (X : M4 k) : Prop := ∀ i j : Fin 4, i.1 < 2 → 2 ≤ j.1 → X i j = 0

private noncomputable def comb (A B : M4 k) : M4 k[X] := Matrix.of fun i j => C (A i j) + X * C (B i j - A i j)

private theorem comb_apply (A B : M4 k) (i j : Fin 4) : comb A B i j = C (A i j) + X * C (B i j - A i j) := rfl

private theorem comb_eq (A B : M4 k) : comb A B = A.map C + (X : k[X]) • (B - A).map C := by
  ext1 i j; simp [comb_apply]

private theorem blk_mul {A B : M4 k} (hA : GlobalTheory A) (hB : GlobalTheory B) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l.1 2 with h | h
  · rw [hB l j (Or.inl h), mul_zero]
  · rw [hA i l (Or.inr h), zero_mul]

private theorem blk_par {A B : M4 k} (hA : GlobalTheory A) (hB : Par B) : GlobalTheory (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases hij with h | h
  · rw [hA i l (Or.inl h), zero_mul]
  rcases lt_or_ge l.1 2 with h' | h'
  · rw [hB l j h' h, mul_zero]
  · rw [hA i l (Or.inr h'), zero_mul]

private theorem par_blk {A B : M4 k} (hA : Par A) (hB : GlobalTheory B) : GlobalTheory (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases hij with h | h
  · rcases lt_or_ge l.1 2 with h' | h'
    · rw [hB l j (Or.inl h'), mul_zero]
    · rw [hA i l h h', zero_mul]
  · rw [hB l j (Or.inr h), mul_zero]

private theorem blk_sub_mul {A B A' B' : M4 k} (hA : Par A) (hB' : Par B') (h : GlobalTheory (B - A)) (h' : GlobalTheory (B' - A')) :
    GlobalTheory (B * B' - A * A') := by
  have e : B * B' - A * A' = (B - A) * B' + A * (B' - A') := by noncomm_ring
  intro i j hij
  rw [e, Matrix.add_apply, blk_par h hB' i j hij, par_blk hA h' i j hij, add_zero]

private theorem comb_mul {A B A' B' : M4 k} (h : GlobalTheory (B - A)) (h' : GlobalTheory (B' - A')) :
    comb A B * comb A' B' = comb (A * A') (B * B') := by
  have h0 := blk_mul h h'
  have e : B * B' - A * A' = (B - A) * A' + A * (B' - A') + (B - A) * (B' - A') := by noncomm_ring
  rw [h0, add_zero] at e
  have h1 : ((B - A).map C : M4 k[X]) * (B' - A').map C = 0 := by
    rw [← Matrix.map_mul, h0]; ext1 i j; simp
  simp only [comb_eq]
  rw [e, Matrix.map_add _ (fun a b => map_add C a b), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h1, smul_zero, add_zero, smul_add]
  abel

private theorem adj_comb (A B : M4 k) : adj (comb A B) = comb (adj A) (adj B) := by
  ext1 i j
  simp only [adj_apply, comb_apply, zsmul_eq_mul, map_sub, map_mul, map_intCast]
  ring

private theorem blk_adj {A B : M4 k} (h : GlobalTheory (B - A)) : GlobalTheory (adj B - adj A) := by
  intro i j hij
  have := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
  rw [Matrix.sub_apply] at this ⊢
  rw [adj_apply, adj_apply, ← smul_sub, this, smul_zero]

private theorem par_adj {A : M4 k} (h : Par A) : Par (adj A) := by
  intro i j hi hj
  rw [adj_apply, h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega), smul_zero]

private theorem comb_same {A B : M4 k} {i j : Fin 4} {x : k} (hA : A i j = x) (hB : B i j = x) :
    comb A B i j = C x := by
  simp [comb_apply, hA, hB]

private theorem comb_gsp {A B : M4 k} {ν : k} (h : GlobalTheory (B - A)) (hA : IsGSp ν A) (hB : IsGSp ν B) :
    IsGSp (C ν) (comb A B) := by
  unfold IsGSp at *
  rw [adj_comb, comb_mul (blk_adj h) h, hA, hB]
  ext1 i j
  rw [comb_same rfl rfl]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem e32 {A : M4 k} {ν : k} (hA : IsGSp ν A) (lo : ∀ i j, i < j → A i j = 0) :
    A 3 2 * A 0 0 + A 2 2 * A 1 0 = 0 := by
  have := congrFun (congrFun hA 1) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, lo 1 2 (by decide), lo 0 2 (by decide)] using this

private theorem blk_of {A B : M4 k} {ν : k} (hA : IsGSp ν A) (hB : IsGSp ν B) (lA : ∀ i j, i < j → A i j = 0)
    (lB : ∀ i j, i < j → B i j = 0) (d : ∀ i, A i i = B i i) (d0 : A 0 0 ≠ 0) (e : A 1 0 = B 1 0) : GlobalTheory (B - A) := by
  have h32 : B 3 2 = A 3 2 := by
    have h1 := e32 hA lA
    have h2 := e32 hB lB
    rw [← d, ← d, ← e] at h2
    exact mul_right_cancel₀ d0 (by linear_combination h2 - h1)
  intro i j hij
  rw [Matrix.sub_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [lA i j h, lB i j h, sub_zero]
  · subst h; rw [d, sub_self]
  · have : (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by revert i j; decide
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e, sub_self]
    · rw [h32, sub_self]

private theorem low_of {A : M4 k} (h : SuppM nM A) : ∀ i j, i < j → A i j = 0 := fun i j hij =>
  h i j hij.ne (by revert i j; decide)

private theorem par_of {A : M4 k} (h : ∀ i j, i < j → A i j = 0) : Par A := fun i j hi hj =>
  h i j (by rw [Fin.lt_def]; omega)

private theorem lc_of {Γ : Type} [TopologicalSpace Γ] {f : Γ → k} (h : AdicCont (⊥ : Ideal k) f) :
    IsLocallyConstant f := by
  have h1 := h 1
  refine IsLocallyConstant.desc f _ h1 fun x y hxy => ?_
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot] at hxy
  exact sub_eq_zero.mp hxy

end UpperTheory.V.Ws.LineM

open UpperTheory.V.Ws.LineM in
theorem UpperTheory.V.Ws.lineM :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ c c' : PD Φ.ι Γ k, Φ.IsRes a c → Φ.IsRes a c' → Supp nM c.r → Supp nM c'.r → c.SameAl c' → Φ.Linked a c c' := by
  intro O Γ _ _ _ _ _ _ Φ k _ a _ c c' hc hc' hs hs' hal
  have lr := fun g => low_of (hs g)
  have lr' := fun g => low_of (hs' g)
  have br : ∀ g, GlobalTheory (c'.r g - c.r g) := fun g =>
    blk_of (hc.pair.mult g) (hc'.pair.mult g) (lr g) (lr' g)
      (fun i => by rw [hc.res.diag, hc'.res.diag])
      (by rw [hc.res.diag]; exact ((Φ.χ 0 g).isUnit.map a).ne_zero) (hal.1 g)
  have bn : ∀ v, GlobalTheory (c'.n v - c.n v) := fun v =>
    blk_of (hc.pair.low v).1 (hc'.pair.low v).1 (hc.pair.low v).2.2 (hc'.pair.low v).2.2
      (fun i => by rw [(hc.pair.low v).2.1, (hc'.pair.low v).2.1])
      (by rw [(hc.pair.low v).2.1]; exact one_ne_zero) (hal.2 v)
  let ρ : Γ →* M4 k[X] :=
    { toFun := fun g => comb (c.r g) (c'.r g)
      map_one' := by
        ext1 i j
        rw [map_one, map_one, comb_same rfl rfl]
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      map_mul' := fun g h => by rw [map_mul, map_mul, comb_mul (br g) (br h)] }
  let P : PD Φ.ι Γ k[X] := ⟨ρ, fun v => comb (c.n v) (c'.n v)⟩
  have Pr : ∀ g, P.r g = comb (c.r g) (c'.r g) := fun _ => rfl
  have Pn : ∀ v, P.n v = comb (c.n v) (c'.n v) := fun _ => rfl
  have conj : ∀ v s, adj (P.n v) * P.r s * P.n v =
      comb (adj (c.n v) * c.r s * c.n v) (adj (c'.n v) * c'.r s * c'.n v) := fun v s => by
    rw [Pr, Pn, adj_comb, comb_mul (blk_adj (bn v)) (br s),
      comb_mul (blk_sub_mul (par_adj (par_of (hc.pair.low v).2.2)) (par_of (lr' s)) (blk_adj (bn v)) (br s)) (bn v)]
  refine ⟨P, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, Or.inr ?_⟩, ?_⟩, ?_, ?_⟩
  · intro g
    exact comb_gsp (br g) (hc.pair.mult g) (hc'.pair.mult g)
  · intro g hg
    rw [Pr, hc.pair.kill g hg, hc'.pair.kill g hg]
    ext1 i j
    rw [comb_same rfl rfl]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  · intro i j hij
    rw [Pr, comb_same (hc.pair.nrm hij) (hc'.pair.nrm hij), map_zero]
  · intro v
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · have := comb_gsp (bn v) (hc.pair.low v).1 (hc'.pair.low v).1
      rwa [map_one] at this
    · rw [Pn, comb_same ((hc.pair.low v).2.1 i) ((hc'.pair.low v).2.1 i), map_one]
    · rw [Pn, comb_same ((hc.pair.low v).2.2 i j hij) ((hc'.pair.low v).2.2 i j hij), map_zero]
  · intro v s hs i j hij
    rw [conj, comb_same (hc.pair.flag v s hs i j hij) (hc'.pair.flag v s hs i j hij), map_zero]
  · intro v s hs i
    unfold PD.ψ
    rw [conj, comb_same (hc.pair.mu v s hs i) (hc'.pair.mu v s hs i), map_one]
  · intro g i
    rw [Pr, comb_same (hc.res.diag g i) (hc'.res.diag g i)]; rfl
  · intro v s hs i
    unfold PD.ψ
    rw [conj, comb_same (hc.res.char v s hs i) (hc'.res.char v s hs i)]; rfl
  · intro g i j hij hw
    rw [Pr, comb_same (hs g i j hij hw) (hs' g i j hij hw), map_zero]
  · intro i j N
    exact ((lc_of (hc.cont i j)).prodMk (lc_of (hc'.cont i j))).comp
      fun x : k × k => Ideal.Quotient.mk ((⊥ : Ideal k[X]) ^ N) (C x.1 + X * C (x.2 - x.1))
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, Pr, comb_apply]
    · funext v; ext i j
      simp [PD.map, Pn, comb_apply]
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, Pr, comb_apply]
    · funext v; ext i j
      simp [PD.map, Pn, comb_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AffSmulOne
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section

variable {R : Type} [CommRing R]

private noncomputable def aff (x y : M4 R) : M4 R[X] := Matrix.of fun i j => (1 - X) * C (x i j) + X * C (y i j)

private theorem aff_apply (x y : M4 R) (i j : Fin 4) : aff x y i j = (1 - X) * C (x i j) + X * C (y i j) := rfl

private theorem aff_eq {x y : M4 R} {i j : Fin 4} {c : R} (hx : x i j = c) (hy : y i j = c) : aff x y i j = C c := by
  rw [aff_apply, hx, hy]; ring

private theorem aff_zero {x y : M4 R} {i j : Fin 4} (hx : x i j = 0) (hy : y i j = 0) : aff x y i j = 0 := by
  rw [aff_apply, hx, hy]
  simp

private theorem aff_smul_one (c : R) : aff (c • (1 : M4 R)) (c • 1) = (C c : R[X]) • (1 : M4 R[X]) := by
  refine Matrix.ext fun i j => ?_
  rw [aff_apply]
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [h]

private theorem aff_one : aff (1 : M4 R) 1 = 1 := by
  ext i j
  rw [aff_apply]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

private theorem adj_aff (x y : M4 R) : adj (aff x y) = aff (adj x) (adj y) := by
  ext i j
  rw [adj_apply, aff_apply, aff_apply, adj_apply, adj_apply, map_zsmul, map_zsmul, smul_add,
    mul_smul_comm, mul_smul_comm]

private structure Cong (x y : M4 R) : Prop where
  x01 : x 0 1 = 0
  x03 : x 0 3 = 0
  x21 : x 2 1 = 0
  x23 : x 2 3 = 0
  y01 : y 0 1 = 0
  y03 : y 0 3 = 0
  y21 : y 2 1 = 0
  y23 : y 2 3 = 0
  e00 : x 0 0 = y 0 0
  e02 : x 0 2 = y 0 2
  e20 : x 2 0 = y 2 0
  e22 : x 2 2 = y 2 2
  e11 : x 1 1 = y 1 1
  e13 : x 1 3 = y 1 3
  e31 : x 3 1 = y 3 1
  e33 : x 3 3 = y 3 3

private theorem Cong.adj {x y : M4 R} (h : Cong x y) : Cong (adj x) (adj y) := by
  have r0 : (0 : Fin 4).rev = 3 := rfl
  have r1 : (1 : Fin 4).rev = 2 := rfl
  have r2 : (2 : Fin 4).rev = 1 := rfl
  have r3 : (3 : Fin 4).rev = 0 := rfl
  constructor <;> simp only [adj_apply, r0, r1, r2, r3, h.x01, h.x03, h.x21, h.x23, h.y01, h.y03,
    h.y21, h.y23, h.e00, h.e02, h.e20, h.e22, h.e11, h.e13, h.e31, h.e33, smul_zero]

private theorem Cong.mul {x y z w : M4 R} (h : Cong x y) (h' : Cong z w) : Cong (x * z) (y * w) := by
  constructor <;> simp only [Matrix.mul_apply, Fin.sum_univ_four, h.x01, h.x03, h.x21, h.x23, h.y01,
    h.y03, h.y21, h.y23, h.e00, h.e02, h.e20, h.e22, h.e11, h.e13, h.e31, h.e33, h'.x01, h'.x03,
    h'.x21, h'.x23, h'.y01, h'.y03, h'.y21, h'.y23, h'.e00, h'.e02, h'.e20, h'.e22, h'.e11, h'.e13,
    h'.e31, h'.e33, mul_zero, zero_mul, add_zero, zero_add]

private theorem Cong.aff_mul {x y z w : M4 R} (h : Cong x y) (h' : Cong z w) :
    aff x y * aff z w = aff (x * z) (y * w) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, d1, d2, d3, d4, d5, d6, d7, d8⟩ := h'
  refine Matrix.ext fun i j => ?_
  simp only [aff_apply, Matrix.mul_apply, Fin.sum_univ_four, map_add (f := _), map_mul]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, map_zero, *] <;> ring

private theorem entries_zero_and_relation_of_suppM_of_isGSp {x : M4 R} {ν : R} (hx : SuppM nP x) (gx : IsGSp ν x) :
    x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 0 3 = 0 ∧ x 1 3 = 0 ∧ x 2 1 = 0 ∧ x 2 3 = 0 ∧
      x 0 0 * x 3 1 = x 1 1 * x 2 0 := by
  have r0 : (0 : Fin 4).rev = 3 := rfl
  have r1 : (1 : Fin 4).rev = 2 := rfl
  have r2 : (2 : Fin 4).rev = 1 := rfl
  have r3 : (3 : Fin 4).rev = 0 := rfl
  have s0 : sgn 0 = 1 := rfl
  have s1 : sgn 1 = 1 := rfl
  have s2 : sgn 2 = -1 := rfl
  have s3 : sgn 3 = -1 := rfl
  have a01 : x 0 1 = 0 := hx 0 1 (by decide) (by decide)
  have a02 : x 0 2 = 0 := hx 0 2 (by decide) (by decide)
  have a03 : x 0 3 = 0 := hx 0 3 (by decide) (by decide)
  have a13 : x 1 3 = 0 := hx 1 3 (by decide) (by decide)
  have a21 : x 2 1 = 0 := hx 2 1 (by decide) (by decide)
  have a23 : x 2 3 = 0 := hx 2 3 (by decide) (by decide)
  have ex := congrArg (fun m : M4 R => m 2 0) gx
  simp [IsGSp, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, r0, r1, r2, r3, s0, s1, s2, s3,
    a01, a02, a03, a13, a21, a23] at ex
  refine ⟨a01, a02, a03, a13, a21, a23, ?_⟩
  linear_combination -ex

private theorem cong_of {x y : M4 R} {ν ν' : R} (hx : SuppM nP x) (hy : SuppM nP y) (gx : IsGSp ν x) (gy : IsGSp ν' y)
    (hd : ∀ i, x i i = y i i) (hu : IsUnit (x 0 0)) (h20 : x 2 0 = y 2 0) : Cong x y := by
  obtain ⟨a01, a02, a03, a13, a21, a23, ax⟩ := entries_zero_and_relation_of_suppM_of_isGSp hx gx
  obtain ⟨b01, b02, b03, b13, b21, b23, bx⟩ := entries_zero_and_relation_of_suppM_of_isGSp hy gy
  refine ⟨a01, a03, a21, a23, b01, b03, b21, b23, hd 0, a02.trans b02.symm, h20, hd 2, hd 1,
    a13.trans b13.symm, ?_, hd 3⟩
  refine hu.mul_left_cancel ?_
  rw [ax, hd 0, bx, hd 1, h20]

private theorem supp_nP {x : M4 R} (h : SuppM qQ x) : SuppM nP x := by
  intro i j hij hw
  refine h i j hij fun hq => hw ?_
  simp only [qQ, nP, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  tauto

private theorem lc_of_cont {Γ : Type} [TopologicalSpace Γ] {f : Γ → R} (h : AdicCont ⊥ f) : IsLocallyConstant f := by
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

end

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.lineP :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ c c' : PD Φ.ι Γ k, Φ.IsRes a c → Φ.IsRes a c' → c.In nP → c'.In nP → c.SamePs c' → Φ.Linked a c c' := by
  intro O Γ _ _ _ _ _ _ Φ k _ a hΦ c c' hc hc' hin hin' hs
  have cong : ∀ g, Cong (c.r g) (c'.r g) := fun g =>
    cong_of (hin.1 g) (hin'.1 g) (hc.pair.mult g) (hc'.pair.mult g)
      (fun i => (hc.res.diag g i).trans (hc'.res.diag g i).symm)
      (by rw [hc.res.diag g 0]; exact (Φ.χ 0 g).isUnit.map a) (hs.1 g)
  have congN : ∀ v, Cong (c.n v) (c'.n v) := fun v =>
    cong_of (supp_nP (hin.2 v)) (supp_nP (hin'.2 v)) (hc.pair.low v).1 (hc'.pair.low v).1
      (fun i => ((hc.pair.low v).2.1 i).trans ((hc'.pair.low v).2.1 i).symm)
      (by rw [(hc.pair.low v).2.1 0]; exact isUnit_one) (hs.2 v)
  have gsp : ∀ {x y : M4 k} {ν : k}, Cong x y → IsGSp ν x → IsGSp ν y → IsGSp (C ν) (aff x y) := by
    intro x y ν h gx gy
    unfold IsGSp at *
    rw [adj_aff, h.adj.aff_mul h, gx, gy, aff_smul_one]
  obtain ⟨ρ, hr⟩ : ∃ ρ : Γ →* M4 k[X], ∀ g, ρ g = aff (c.r g) (c'.r g) :=
    ⟨{ toFun := fun g => aff (c.r g) (c'.r g)
       map_one' := by
         show aff (c.r 1) (c'.r 1) = 1
         rw [map_one, map_one, aff_one]
       map_mul' := fun g h => by
         show aff (c.r (g * h)) (c'.r (g * h)) = aff (c.r g) (c'.r g) * aff (c.r h) (c'.r h)
         rw [map_mul, map_mul, (cong g).aff_mul (cong h)] }, fun _ => rfl⟩
  have conj : ∀ v s, adj (aff (c.n v) (c'.n v)) * ρ s * aff (c.n v) (c'.n v) =
      aff (adj (c.n v) * c.r s * c.n v) (adj (c'.n v) * c'.r s * c'.n v) := by
    intro v s
    rw [hr, adj_aff, (congN v).adj.aff_mul (cong s), ((congN v).adj.mul (cong s)).aff_mul (congN v)]
  refine ⟨⟨ρ, fun v => aff (c.n v) (c'.n v)⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro g
    dsimp only
    rw [hr]
    exact gsp (cong g) (hc.pair.mult g) (hc'.pair.mult g)
  · intro g hg
    dsimp only
    rw [hr, hc.pair.kill g hg, hc'.pair.kill g hg, aff_one]
  · intro i j hij
    dsimp only
    rw [hr]
    exact aff_zero (hc.pair.nrm hij) (hc'.pair.nrm hij)
  · intro v
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · have h1 := gsp (congN v) (hc.pair.low v).1 (hc'.pair.low v).1
      rwa [map_one] at h1
    · exact (aff_eq ((hc.pair.low v).2.1 i) ((hc'.pair.low v).2.1 i)).trans (map_one C)
    · exact aff_zero ((hc.pair.low v).2.2 i j hij) ((hc'.pair.low v).2.2 i j hij)
  · intro v s hs' i j hij
    dsimp only
    rw [conj]
    exact aff_zero (hc.pair.flag v s hs' i j hij) (hc'.pair.flag v s hs' i j hij)
  · intro v s hs' i
    unfold PD.ψ
    dsimp only
    rw [conj]
    exact (aff_eq (hc.pair.mu v s hs' i) (hc'.pair.mu v s hs' i)).trans (map_one C)
  · intro g i
    dsimp only
    rw [hr]
    exact aff_eq (hc.res.diag g i) (hc'.res.diag g i)
  · intro v s hs' i
    unfold PD.ψ
    dsimp only
    rw [conj]
    exact aff_eq (hc.res.char v s hs' i) (hc'.res.char v s hs' i)
  · left
    refine ⟨fun g i j hij hw => ?_, fun v i j hij hw => ?_⟩
    · dsimp only
      rw [hr]
      exact aff_zero (hin.1 g i j hij hw) (hin'.1 g i j hij hw)
    · exact aff_zero (hin.2 v i j hij hw) (hin'.2 v i j hij hw)
  · intro i j N
    have l1 := lc_of_cont (hc.cont i j)
    have l2 := lc_of_cont (hc'.cont i j)
    have l3 := IsLocallyConstant.comp₂ l1 l2
      (fun u w => Ideal.Quotient.mk ((⊥ : Ideal k[X]) ^ N) ((1 - X) * C u + X * C w))
    dsimp only
    simp only [hr, aff_apply]
    exact l3
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, mapRep, hr, aff_apply]
    · funext v
      ext i j
      simp [PD.map, aff_apply]
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, mapRep, hr, aff_apply]
    · funext v
      ext i j
      simp [PD.map, aff_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PureDet
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def eAB : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem cp_block {K : Type} [Field K] (X : M4 K) (h : IsBlock X) :
    X.charpoly = (X.submatrix ixA ixA).charpoly * (X.submatrix ixB ixB).charpoly := by
  have e : Matrix.reindex eAB.symm eAB.symm X =
      Matrix.fromBlocks (X.submatrix ixA ixA) (X.submatrix ixA ixB) 0 (X.submatrix ixB ixB) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact h (ixB i) (ixA j) (by revert i j; decide)
    · rfl
  rw [← Matrix.charpoly_reindex eAB.symm, e, Matrix.charpoly_fromBlocks_zero₂₁]

private theorem det_two {K : Type} [Field K] [IsAlgClosed K] (A : Matrix (Fin 2) (Fin 2) K) :
    ∃ a ∈ A.charpoly.roots, ∃ b ∈ A.charpoly.roots, A.det = a * b := by
  have hc : A.charpoly.roots.card = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hc
  refine ⟨a, by simp [hab], b, by simp [hab], ?_⟩
  rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp

theorem UpperTheory.V.Ws.pureDet :
    ∀ {K : Type} [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (X : M4 K), IsBlock X →
          (∀ x ∈ X.charpoly.roots, ∀ y ∈ X.charpoly.roots, ‖ι x‖ = ‖ι y‖) →
          ‖ι (X.submatrix ixA ixA).det‖ = ‖ι (X.submatrix ixB ixB).det‖ := by
  intro K _ _ ι X hX h
  have hr : X.charpoly.roots =
      (X.submatrix ixA ixA).charpoly.roots + (X.submatrix ixB ixB).charpoly.roots := by
    rw [cp_block X hX, roots_mul (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero)]
  obtain ⟨a, ha, b, hb, hA⟩ := det_two (X.submatrix ixA ixA)
  obtain ⟨c, hc, d, hd, hB⟩ := det_two (X.submatrix ixB ixB)
  rw [hr] at h
  rw [hA, hB, map_mul, map_mul, norm_mul, norm_mul,
    h a (Multiset.mem_add.2 (Or.inl ha)) c (Multiset.mem_add.2 (Or.inr hc)),
    h b (Multiset.mem_add.2 (Or.inl hb)) d (Multiset.mem_add.2 (Or.inr hd))]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockDet
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem bd_up_mul {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) : IsUp (Y * Z) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : k < i
  · rw [hY i k h, zero_mul]
  · rw [hZ k j (lt_of_lt_of_le hij (not_lt.mp h)), mul_zero]

private theorem bd_up_diag {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) (i : Fin 4) : (Y * Z) i i = Y i i * Z i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hY i k h, zero_mul]
  · rw [hZ k i h, mul_zero]

private theorem bd_conj_mul {u v : M4 R} (h : u * v = 1) (Y Z : M4 R) :
    v * (Y * Z) * u = (v * Y * u) * (v * Z * u) := by
  have : (v * Y * u) * (v * Z * u) = v * Y * (u * v) * Z * u := by simp only [Matrix.mul_assoc]
  rw [this, h]; simp only [Matrix.mul_assoc, Matrix.one_mul]

private theorem bd_trace {u v : M4 R} (h : u * v = 1) (Y : M4 R) : (v * Y * u).trace = Y.trace := by
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]

private theorem bd_key {u v N X : M4 R} (h : u * v = 1) (hN : IsUp (v * N * u)) (hX : IsUp (v * X * u)) :
    (N * X).trace ^ 2 - ((N * X) * (N * X)).trace =
      (∑ i, (v * N * u) i i * (v * X * u) i i) ^ 2 - ∑ i, ((v * N * u) i i * (v * X * u) i i) ^ 2 := by
  have hU := bd_up_mul hN hX
  rw [← bd_trace h (N * X), ← bd_trace h ((N * X) * (N * X)), bd_conj_mul h (N * X), bd_conj_mul h N X]
  simp only [Matrix.trace, Matrix.diag_apply, bd_up_diag hU hU, bd_up_diag hN hX, sq]

private theorem bd_poly {u v S : M4 R} (h : u * v = 1) (h' : v * u = 1) (b c : R) :
    v * (S * S - b • S + c • (1 : M4 R)) * u = (v * S * u) * (v * S * u) - b • (v * S * u) + c • (1 : M4 R) := by
  rw [← bd_conj_mul h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h']

private theorem bd_poly_up {T : M4 R} (hT : IsUp T) (b c : R) : IsUp (T * T - b • T + c • (1 : M4 R)) := by
  intro i j hij
  simp [bd_up_mul hT hT i j hij, hT i j hij, Matrix.one_apply_ne hij.ne']

private theorem bd_poly_diag {T : M4 R} (hT : IsUp T) (b c : R) (i : Fin 4) :
    (T * T - b • T + c • (1 : M4 R)) i i = T i i * T i i - b * T i i + c := by
  simp [bd_up_diag hT hT]

private theorem bd_notMem (m : Ideal R) [hm : m.IsPrime] {t x p q p' q' r s : R} (ht : t - x ∈ m) (hp : p' - p ∈ m)
    (hq : q' - q ∈ m) (hr : r ∈ m) (h1 : x - p ∉ m) (h2 : x - q ∉ m) :
    t * t - (p' + q') * t + (p' * q' - r * s) ≠ 0 := by
  intro h0
  have e : (x - p) * (x - q) ∈ m := by
    rw [← Ideal.Quotient.eq] at ht hp hq
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hr ⊢
    have := congrArg (Ideal.Quotient.mk m) h0
    simp only [map_add (f := _), map_sub, map_mul, map_zero, ht, hp, hq, hr] at this ⊢
    linear_combination this
  rcases hm.mem_or_mem e with e | e
  · exact h1 e
  · exact h2 e

private theorem bd_zero {S : M4 R} (h : IsBlock S) : S 0 1 = 0 ∧ S 0 3 = 0 ∧ S 1 0 = 0 ∧ S 1 2 = 0 ∧ S 2 1 = 0 ∧
    S 2 3 = 0 ∧ S 3 0 = 0 ∧ S 3 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact h _ _ (by decide)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.blockDet :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (m : Ideal R) [m.IsPrime] (a : Fin 4 → R) (u v S X : M4 R), v * u = 1 →
          (∀ i j, lamW i ≠ lamW j → a i - a j ∉ m) → IsBlock S → (∀ i j, S i j - Matrix.diagonal a i j ∈ m) → IsUp (v * S * u) →
          (∀ i, (v * S * u) i i - a i ∈ m) → IsBlock X → IsUp (v * X * u) →
          (X.submatrix ixA ixA).det = (v * X * u) 0 0 * (v * X * u) 2 2 ∧ (X.submatrix ixB ixB).det = (v * X * u) 1 1 * (v * X * u) 3 3 := by
  intro R _ _ _ m _ a u v S X hvu ha hS hSa hT hTa hX hY
  have huv : u * v = 1 := mul_eq_one_comm.mp hvu
  obtain ⟨s01, s03, s10, s12, s21, s23, s30, s32⟩ := bd_zero hS
  obtain ⟨x01, x03, x10, x12, x21, x23, x30, x32⟩ := bd_zero hX
  have hd : ∀ i, S i i - a i ∈ m := fun i => by simpa using hSa i i
  have h13 : S 1 3 ∈ m := by simpa using hSa 1 3
  have h02 : S 0 2 ∈ m := by simpa using hSa 0 2
  obtain ⟨N, hN⟩ : ∃ N, N = S * S - (S 1 1 + S 3 3) • S + (S 1 1 * S 3 3 - S 1 3 * S 3 1) • (1 : M4 R) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ N, N = S * S - (S 0 0 + S 2 2) • S + (S 0 0 * S 2 2 - S 0 2 * S 2 0) • (1 : M4 R) := ⟨_, rfl⟩
  have hNz : ∀ i j, (lamW i = 0 ∨ lamW j = 0) → N i j = 0 := by
    intro i j h
    subst hN
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hMz : ∀ i j, (lamW i = 1 ∨ lamW j = 1) → M i j = 0 := by
    intro i j h
    subst hM
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hNM : N * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four, hMz 0 j (Or.inl rfl), hMz 2 j (Or.inl rfl), hNz i 1 (Or.inr rfl),
      hNz i 3 (Or.inr rfl)]
    simp
  have uN : IsUp (v * N * u) := by rw [hN, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have uM : IsUp (v * M * u) := by rw [hM, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have nN : ∀ i, lamW i = 1 → (v * N * u) i i ≠ 0 := by
    intro i hi
    rw [hN, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 1) (hd 3) h13 (ha i 1 (by rw [hi]; decide)) (ha i 3 (by rw [hi]; decide))
  have nM : ∀ i, lamW i = 0 → (v * M * u) i i ≠ 0 := by
    intro i hi
    rw [hM, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 0) (hd 2) h02 (ha i 0 (by rw [hi]; decide)) (ha i 2 (by rw [hi]; decide))
  have hz : ∀ i, (v * N * u) i i * (v * M * u) i i = 0 := by
    intro i
    rw [← bd_up_diag uN uM, ← bd_conj_mul huv, hNM]; simp
  have n1 : (v * N * u) 1 1 = 0 := (mul_eq_zero.mp (hz 1)).resolve_right (nM 1 rfl)
  have n3 : (v * N * u) 3 3 = 0 := (mul_eq_zero.mp (hz 3)).resolve_right (nM 3 rfl)
  have m0 : (v * M * u) 0 0 = 0 := (mul_eq_zero.mp (hz 0)).resolve_left (nN 0 rfl)
  have m2 : (v * M * u) 2 2 = 0 := (mul_eq_zero.mp (hz 2)).resolve_left (nN 2 rfl)
  have u1 : IsUp (v * 1 * u) := by
    rw [Matrix.mul_one, hvu]; intro i j hij; exact Matrix.one_apply_ne hij.ne'
  have two : (2 : R) ≠ 0 := two_ne_zero
  constructor
  · have k1 := bd_key huv uN u1
    have k2 := bd_key huv uN hY
    have z1 : ∀ i, N i 1 = 0 := fun i => hNz i 1 (Or.inr rfl)
    have z3 : ∀ i, N i 3 = 0 := fun i => hNz i 3 (Or.inr rfl)
    have z1' : ∀ i, N 1 i = 0 := fun i => hNz 1 i (Or.inl rfl)
    have z3' : ∀ i, N 3 i = 0 := fun i => hNz 3 i (Or.inl rfl)
    have p0 := nN 0 rfl
    have p2 := nN 2 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * N * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', n1, n3, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixA, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 0 0 * X 2 2 - X 0 2 * X 2 0) * k1
  · have k1 := bd_key huv uM u1
    have k2 := bd_key huv uM hY
    have z1 : ∀ i, M i 0 = 0 := fun i => hMz i 0 (Or.inr rfl)
    have z3 : ∀ i, M i 2 = 0 := fun i => hMz i 2 (Or.inr rfl)
    have z1' : ∀ i, M 0 i = 0 := fun i => hMz 0 i (Or.inl rfl)
    have z3' : ∀ i, M 2 i = 0 := fun i => hMz 2 i (Or.inl rfl)
    have p0 := nM 1 rfl
    have p2 := nM 3 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * M * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', m0, m2, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixB, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 1 1 * X 3 3 - X 1 3 * X 3 1) * k1
end

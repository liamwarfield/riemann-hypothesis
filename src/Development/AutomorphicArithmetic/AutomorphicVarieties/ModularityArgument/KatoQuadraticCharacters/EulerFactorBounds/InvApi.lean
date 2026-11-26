module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb.InverseLimitApi

private def Fm (R : Type) [CommRing R] (w : ℕ) : Submodule R ((Fin 2 → R) → R) :=
  Submodule.span R {φ | ∃ i j : ℕ, i + j = w ∧ φ = fun u => u 0 ^ i * u 1 ^ j}

private theorem fm_mul {R : Type} [CommRing R] {a b : ℕ} {φ ψ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R a) (hψ : ψ ∈ Fm R b) :
    φ * ψ ∈ Fm R (a + b) := by
  induction hφ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul k x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | mem x hx =>
    induction hψ using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    | mem y hy =>
      obtain ⟨i, j, rfl, rfl⟩ := hx
      obtain ⟨i', j', rfl, rfl⟩ := hy
      refine Submodule.subset_span ⟨i + i', j + j', by omega, ?_⟩
      funext u
      simp only [Pi.mul_apply]
      ring

private theorem fm_pow {R : Type} [CommRing R] {φ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R 1) (k : ℕ) : φ ^ k ∈ Fm R k := by
  induction k with
  | zero => exact Submodule.subset_span ⟨0, 0, rfl, by funext u; simp⟩
  | succ k ih => rw [pow_succ]; exact fm_mul ih hφ

private theorem fm_lin {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (fun u => (m *ᵥ u) i) ∈ Fm R 1 := by
  have h0 : (fun u : Fin 2 → R => u 0 ^ 1 * u 1 ^ 0) ∈ Fm R 1 := Submodule.subset_span ⟨1, 0, rfl, rfl⟩
  have h1 : (fun u : Fin 2 → R => u 0 ^ 0 * u 1 ^ 1) ∈ Fm R 1 := Submodule.subset_span ⟨0, 1, rfl, rfl⟩
  have h := add_mem (Submodule.smul_mem _ (m i 0) h0) (Submodule.smul_mem _ (m i 1) h1)
  convert h using 1
  funext u
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem un_pow (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) (j : ℕ) : f ^ j ∈ X.Un m := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
  induction j with
  | zero => simpa using (h m).1
  | succ j ih => rw [pow_succ]; exact ((h m).2 _ ih _ hf).1

private def Cf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Khat l) where
  carrier := {x | ∃ f ∈ X.Un (l ^ n), Rep X l n f x}
  zero_mem' := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨h1, -, h3, -⟩ := sCls Ω ε X l n
    refine ⟨1, (h _).1, ?_⟩
    simpa using h3 1 _ 0 (h1 1)
  add_mem' := by
    rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨-, h2, -⟩ := sCls Ω ε X l n
    exact ⟨f * g, ((h _).2 f hf g hg).1, (h2 _ _ _ _ ha hb).1⟩
  smul_mem' := by
    rintro k a ⟨f, hf, ha⟩
    obtain ⟨-, -, -, -, -, -, h⟩ := sCls Ω ε X l n
    obtain ⟨j, hj⟩ := h f k a ha
    exact ⟨f ^ j, un_pow X _ f hf j, hj⟩

private def Pm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {t | PolMod X l w n t}
  zero_mem' := ⟨0, fun _ => (Cf X l n).zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c + d, fun i => (Cf X l n).add_mem (hc i) (hd i), fun u => ?_⟩
    simp only [Pi.add_apply, ha u, hb u, smul_add, Finset.sum_add_distrib]
  smul_mem' := by
    rintro k a ⟨c, hc, ha⟩
    refine ⟨k • c, fun i => (Cf X l n).smul_mem k (hc i), fun u => ?_⟩
    simp only [Pi.smul_apply, ha u, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem pm_fm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (c : X.Khat l) (hc : c ∈ Cf X l n)
    (φ : (Fin 2 → ℤ_[l]) → ℤ_[l]) (hφ : φ ∈ Fm ℤ_[l] w) : (fun u => φ u • c) ∈ Pm X l w n := by
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (Pm X l w n).zero_mem using 1
    funext u; simp
  | add x y _ _ hx hy =>
    convert (Pm X l w n).add_mem hx hy using 1
    funext u; simp [add_smul]
  | smul k x _ hx =>
    convert (Pm X l w n).smul_mem k hx using 1
    funext u; simp [mul_smul]
  | mem x hx =>
    obtain ⟨i, j, rfl, rfl⟩ := hx
    refine ⟨Pi.single ⟨i, by omega⟩ c, fun k => ?_, fun u => ?_⟩
    · show Pi.single (M := fun _ => X.Khat l) _ c k ∈ Cf X l n
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
    · rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (i + j + 1))]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, smul_zero]
      · simp

private theorem pm_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (t : X.Fn l)
    (ht : PolMod X l w n t) : PolMod X l w n (X.act l m t) := by
  obtain ⟨c, hc, ht⟩ := ht
  have key : ∀ i : Fin (w + 1), (fun u => (((fun u => (mZl l m *ᵥ u) 0) ^ (i : ℕ) * (fun u => (mZl l m *ᵥ u) 1) ^ (w - (i : ℕ)) :
      (Fin 2 → ℤ_[l]) → ℤ_[l]) u) • X.kmap l (X.sl (toGQ m)).toRingEquiv (c i)) ∈ Pm X l w n := by
    intro i
    apply pm_fm
    · obtain ⟨f, hf, hr⟩ := hc i
      obtain ⟨-, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
      obtain ⟨-, -, -, -, h', -⟩ := sCls Ω ε X l n
      exact ⟨slU X (toGQ m) f, h _ _ f hf, h' (X.sl (toGQ m)).toRingEquiv f _ hr⟩
    · have := fm_mul (fm_pow (fm_lin (mZl l m) 0) i) (fm_pow (fm_lin (mZl l m) 1) (w - i))
      rwa [show (i : ℕ) + (w - i) = w by omega] at this
  have h := (Pm X l w n).sum_mem fun i (_ : i ∈ Finset.univ) => key i
  show X.act l m t ∈ Pm X l w n
  convert h using 1
  funext u
  show X.kmap l (X.sl (toGQ m)).toRingEquiv (t (mZl l m *ᵥ u)) = _
  rw [ht, map_sum (X.kmap l (X.sl (toGQ m)).toRingEquiv), Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

private theorem pm_down (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (t : X.Fn l)
    (ht : PolMod X l w (n + 1) t) : PolMod X l w n t := by
  obtain ⟨c, hc, ht⟩ := ht
  refine ⟨c, fun i => ?_, ht⟩
  obtain ⟨f, hf, hr⟩ := hc i
  obtain ⟨-, -, -, -, -, h, -⟩ := sCls Ω ε X l n
  refine ⟨f, fun W hW => ?_, h _ _ hr⟩
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨g ^ l, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ']
  exact hg

private def Im (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {a | InvM X l N w n a}
  zero_mem' := by
    obtain ⟨he, -⟩ := sApi Ω ε X l n
    refine ⟨⟨0, (Pm X l w n).zero_mem, he.refl _⟩, fun γ _ => ?_, 0, zero_mem _, fun u => by simp⟩
    rw [map_zero]; exact he.refl _
  add_mem' := by
    rintro a b ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩ ⟨⟨s, hs, hbs⟩, hb, y, hy, hyb⟩
    obtain ⟨-, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t + s, (Pm X l w n).add_mem ht hs, (h _ _ _ _ hat hbs).1⟩, fun γ hγ => ?_, x + y, add_mem hx hy, ?_⟩
    · rw [(X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ)).map_add]
      exact (h _ _ _ _ (ha γ hγ) (hb γ hγ)).1
    · have := (h x ((l : ℤ_[l]) ^ cL X l N w • a) y ((l : ℤ_[l]) ^ cL X l N w • b) hxa hyb).1
      rw [← smul_add] at this
      exact this
  smul_mem' := by
    rintro k a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨k • t, (Pm X l w n).smul_mem k ht, h _ _ _ hat⟩, fun γ hγ => ?_, k • x, Submodule.smul_mem _ _ hx, ?_⟩
    · rw [map_smul]; exact h _ _ _ (ha γ hγ)
    · have := h k x ((l : ℤ_[l]) ^ cL X l N w • a) hxa
      rw [smul_comm] at this
      exact this

private theorem main : SInvApi := by
  intro Ω _ _ _ ε X l _ N w n
  refine ⟨(Im X l N w n).zero_mem, fun a b ha hb => ⟨(Im X l N w n).add_mem ha hb, (Im X l N w n).sub_mem ha hb⟩,
    fun k a ha => (Im X l N w n).smul_mem k ha, ?_, fun ι S a h => (Im X l N w n).sum_mem h, ?_, ?_,
    fun m t _ ht => pm_act X l w n m t ht⟩
  · rintro a b hab ⟨⟨t, ht, hbt⟩, hb, x, hx, hxb⟩
    obtain ⟨he, -, hs, -, -, hm, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t, ht, he.trans hab hbt⟩, fun γ hγ => he.trans (hm _ _ _ hab) (he.trans (hb γ hγ) (he.symm hab)), x, hx, ?_⟩
    exact he.trans (x := x) (y := (l : ℤ_[l]) ^ cL X l N w • b) hxb (hs _ _ _ (he.symm hab))
  · rintro a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨t, pm_down X l w n t ht, h _ _ hat⟩, fun γ hγ => h _ _ (ha γ hγ), x, hx,
      h x ((l : ℤ_[l]) ^ cL X l N w • a) hxa⟩
  · intro a
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨0, (Pm X l w 0).zero_mem, h _ _⟩, fun γ _ => h _ _, 0, zero_mem _, h 0 ((l : ℤ_[l]) ^ cL X l N w • a)⟩

end UpperTheory.V.Z.Kato.Nb.InverseLimitApi

theorem UpperTheory.V.Z.Kato.Nb.sInvApi :
    UpperTheory.V.Z.Kato.Nb.SInvApi :=
  UpperTheory.V.Z.Kato.Nb.InverseLimitApi.main

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N : ℕ)

private theorem rep_slD (f : X.Kˣ) :
    Rep X l n (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f) (clsK X l n (slD X N (f : X.K))) :=
  (sCls Ω ε X l n).1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f)

private theorem cgr_rfl {K : Type} [Field K] (m : ℕ) (f : Kˣ) : Cgr m f f := ⟨1, by simp⟩

private theorem term_mul (a a' b b' : X.Kˣ) (h : Cgr (l ^ n) a (a' * b / b')) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N (a : X.K)) -
      (clsK X l n (slD X N (a' : X.K)) + (clsK X l n (slD X N (b : X.K)) - clsK X l n (slD X N (b' : X.K))))) = 0 := by
  obtain ⟨-, hr2, -, hr4, -⟩ := sCls Ω ε X l n
  have ra := rep_slD X l n N a
  have ra' := rep_slD X l n N a'
  have rb := rep_slD X l n N b
  have rb' := rep_slD X l n N b'
  have r1 := (hr2 _ _ _ _ ra' rb).1
  have r2 := (hr2 _ _ _ _ r1 rb').2
  obtain ⟨k, hk⟩ := h
  have hz := hr4 _ _ _ _ ra r2 ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) k, by
    rw [hk, map_mul, map_pow, map_div, map_mul]⟩
  rw [add_sub_assoc] at hz
  exact hz

private theorem term_pow (a : X.Kˣ) (k : ℕ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N ((a ^ k : X.Kˣ) : X.K)) -
      (k : ℤ_[l]) • clsK X l n (slD X N (a : X.K))) = 0 := by
  obtain ⟨-, -, h3, h4, -⟩ := sCls Ω ε X l n
  refine h4 _ _ _ _ (rep_slD X l n N (a ^ k)) (h3 _ _ k (rep_slD X l n N a)) ?_
  rw [map_pow]
  exact cgr_rfl _ _

private theorem term_red (a : X.Kˣ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l (n + 1) (slD X N (a : X.K)) - clsK X l n (slD X N (a : X.K))) = 0 := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := sCls Ω ε X l n
  exact h4 _ _ _ _ (h6 _ _ (rep_slD X l (n + 1) N a)) (rep_slD X l n N a) (cgr_rfl _ _)

end

private theorem fib {ι κ V : Type} [Fintype ι] [Fintype κ] [AddCommMonoid V] (C : ι → Prop) (d : ι → κ) (Q : κ → Prop) (F : ι → V)
    [DecidablePred Q] [DecidablePred fun i => C i ∧ Q (d i)] [∀ z, DecidablePred fun i => C i ∧ d i = z] :
    ∑ i ∈ Finset.univ.filter (fun i => C i ∧ Q (d i)), F i =
      ∑ z ∈ Finset.univ.filter Q, ∑ i ∈ Finset.univ.filter (fun i => C i ∧ d i = z), F i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i => C i ∧ Q (d i))) (t := Finset.univ.filter Q) (g := d)
    (fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.2)]
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiMul :
    UpperTheory.V.Z.Kato.Nb.SXiMul := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y hxy P
  have hOk : ∀ m : GL (Fin 2) (ZMod M), m ∈ Finset.univ.filter
      (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧
        P (Matrix.GeneralLinearGroup.det m)) →
      Ok (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) :=
    fun m hm => (sCdFacts N M₀ M (Lev.eq hL)).2.2.1 m (Finset.mem_filter.1 hm).2.1.1 x y hxy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a' b b' hab u
    simp only [Pi.add_apply, Pi.sub_apply]
    unfold Xi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [← smul_sub, ← smul_add, ← smul_sub, map_smul,
      term_mul X l n N _ _ _ _ (hab _ _ (hOk m hm)), smul_zero]
  · intro a k u
    simp only [Pi.sub_apply, Pi.smul_apply]
    unfold Xi
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m _
    rw [smul_comm (k : ℤ_[l]), ← smul_sub, map_smul, term_pow, smul_zero]
  · intro a u
    unfold Xi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m _
    rw [← smul_sub, map_smul, term_red, smul_zero]
  · intro a A π t _
    funext u
    rw [Finset.sum_apply]
    unfold Xi
    convert fib (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
      (fun m => Matrix.GeneralLinearGroup.det m) (fun z => π z = t) _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SInteg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem root_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ^ (l - 1) = 1) : x ∈ c.O := by
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  haveI : NeZero (l - 1) := ⟨hpos.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hg1 : g ∈ rootsOfUnity (l - 1) (ZMod l) := by
    rw [mem_rootsOfUnity, ← hg, pow_orderOf_eq_one]
  rw [← KStar.TotallyRealRoots.map_red_rootsOfUnity (l := l) dvd_rfl] at hg1
  obtain ⟨ζ, hζ, hζg⟩ := hg1
  have hζ1 : ζ ^ (l - 1) = 1 := hζ
  have hp : IsPrimitiveRoot ζ (l - 1) := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rw [← hg, orderOf_dvd_iff_pow_eq_one, ← hζg, ← map_pow, hk, map_one]
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hq := (IsPrimitiveRoot.coe_units_iff.2 hp).map_of_injective hinj
  obtain ⟨i, -, rfl⟩ := hq.eq_pow_of_pow_eq_one hx
  exact pow_mem (c.O.algebraMap_mem _) i

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem mv_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l}
    (hM : ∀ i k, M i k ∈ c.O) (hv : ∀ k, v k ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hM i k) (hv k)

private def rd (l : ℕ) : (ZMod (l ^ 1))ˣ →* (ZMod l)ˣ :=
  Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom

private theorem rd_val (l : ℕ) [Fact l.Prime] (y : (ZMod (l ^ 1))ˣ) :
    ((rd l y : (ZMod l)ˣ) : ZMod l) = (((y : ZMod (l ^ 1)).val : ℕ) : ZMod l) := by
  rw [ZMod.natCast_val]; rfl

theorem UpperTheory.V.Z.Kato.Nb.sInteg :
    UpperTheory.V.Z.Kato.Nb.SInteg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW
  obtain ⟨-, -, -, -, -, -, hpr, -, -, -, -, χ, -, -, hχ⟩ := hA
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  have hχ' : ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ (rd l (cycMod ℚ Ω l 1 s) : (ZMod l)ˣ) := fun s => by
    rw [rd_val]; exact hχ s
  have hsurj : ∀ u : (ZMod l)ˣ, ∃ s : G ℚ Ω, rd l (cycMod ℚ Ω l 1 s) = u := by
    intro u
    refine ⟨repM l u, ?_⟩
    have h1 := (sCycZ Ω l 1 (repM l u)).1
    have h2 := (hS (l ^ 1) (repM l u)).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [h1]
    exact h2.trans ((hS l 1).2.2.1 u)
  have h1 : ψ 1 = 1 := by
    have := hχ' 1
    rw [map_one, map_one, map_one, Units.val_one, Units.val_one] at this
    exact this.symm
  have hmul : ∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v := by
    intro u v
    obtain ⟨s, rfl⟩ := hsurj u
    obtain ⟨t, rfl⟩ := hsurj v
    rw [← map_mul, ← map_mul, ← hχ', ← hχ', ← hχ', map_mul, Units.val_mul]
  have hpow : ∀ s : G ℚ Ω, χ s ^ (l - 1) = 1 := by
    intro s
    apply Units.ext
    rw [← map_pow, hχ', map_pow, map_pow, ZMod.units_pow_card_sub_one_eq_one, Units.val_one, h1, Units.val_one]
  have hχO : ∀ s : G ℚ Ω, (χ s : Qbar l) ∈ cf.O := fun s =>
    root_mem cf (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])
  have hεO : ∀ s : G ℚ Ω, eps l s ∈ cf.O := fun s => cf.O.algebraMap_mem ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])
  let θ : G ℚ Ω →* (Qbar l)ˣ := (cycBar ℚ Ω l ^ e)⁻¹ * χ
  have hθ : ∀ s, thK l e ψ s = (θ s : Qbar l) := fun s => by
    simp only [thK, θ, ← hχ s, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hθO : ∀ s, (θ s : Qbar l) ∈ cf.O := fun s => by
    have h2 : (θ s : Qbar l) = eps l s⁻¹ ^ e * (χ s : Qbar l) := by
      simp only [θ, eps, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
    rw [h2]
    exact mul_mem (pow_mem (hεO _) e) (hχO s)
  have hθi : ∀ s, (θ s : Qbar l)⁻¹ = (θ s⁻¹ : (Qbar l)ˣ) := fun s => by
    rw [map_inv, Units.val_inv_eq_inv_val]
  have hρO : ∀ s i k, rhoK W e ψ s i k ∈ cf.O := fun s i k => by
    rw [rhoK, hθ, hθi, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (hθO _) (hW s i k)
  refine ⟨fun s => ?_, h1, hmul, fun u => ?_, hρO, fun s t => ?_, fun c₀ Y hY r s y i => ?_⟩
  · have h2 := nle cf (hθO s⁻¹)
    rw [← hθi, norm_inv, inv_le_one₀ (norm_pos_iff.2 (θ s).ne_zero)] at h2
    rw [hθ]
    exact le_antisymm (nle cf (hθO s)) h2
  · obtain ⟨s, rfl⟩ := hsurj u
    rw [← hχ']
    exact hχO s
  · simp only [rhoK, hθ, mat, map_mul, Units.val_mul, mul_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm ((θ s : Qbar l)⁻¹)]
  · obtain ⟨bB, hbB, b, hb, hc⟩ := hY r 0
    have hF : YfB X l pr W e ψ 0 r N bB s y i ∈ cf.O := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.sum_apply]
      refine sum_mem fun z _ => mv_mem cf (hρO _) (fun k => hpr _ (hbB _ ?_).1 k) i
      have hM := hS (topM l 0 r (N * N))
      have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l 0 r (N * N)) (s * t) = _ := fun s t => (hM s).2.1 t
      have hr := (hM 1).2.2.1
      refine (hM _).2.2.2.1.2 ?_
      have h3 := hm (repM (topM l 0 r (N * N)) z) ((repM (topM l 0 r (N * N)) z)⁻¹ * s *
        repM (topM l 0 r (N * N)) (z * (cycM (topM l 0 r (N * N)) s)⁻¹))
      rw [← mul_assoc, mul_inv_cancel_left, hm, hr, hr, mul_left_comm, mul_inv_cancel, mul_one] at h3
      exact (mul_eq_left.1 h3.symm)
    have h4 := hc s y i
    have h5 := nle cf (add_mem hF (sub_mem (mv_mem cf (hρO s) (hb (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) i) (hb y i)))
    rw [Cg, pow_zero, norm_one] at h4
    have h7 : ∀ a a' : Qbar l, ‖a - a'‖ ≤ 1 → ‖a'‖ ≤ 1 → ‖a‖ ≤ 1 := fun a a' ha ha' => by
      have h6 := (IsUltrametricDist.norm_add_le_max (a - a') a').trans (max_le ha ha')
      rwa [sub_add_cancel] at h6
    exact h7 _ _ h4 h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ValCast
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem term {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N : ℕ) (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.Kˣ) (c : ℕ) (k k' : ℤ_[l]) (h : (l : ℤ_[l]) ^ n ∣ k * c - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      X.kmap l (X.gal s) (k' • clsK X l n (slD X N (f : X.K)))) = 0 := by
  obtain ⟨hRep, -, hPow, hUniq, hMap, -, -⟩ := sCls Ω ε X l n
  obtain ⟨hGalSl, -⟩ := sSlD Ω ε X N hN
  have hApi := (sApi Ω ε X l n).2.2.2.2.1
  have hmul : ∀ a b : X.K, slD X N (a * b) = slD X N a * slD X N b := by
    intro a b
    simp [slD]
  have h1 : slD X N 1 = 1 := by simp [slD]
  have hpow : ∀ (a : X.K) (m : ℕ), slD X N (a ^ m) = slD X N a ^ m := by
    intro a m
    simp [slD]
  let U : X.Kˣ → X.Kˣ := fun u =>
    ⟨slD X N u, slD X N ↑u⁻¹, by rw [← hmul]; simp [h1], by rw [← hmul]; simp [h1]⟩
  have hA := hRep (U (galU X s f ^ c))
  have hB := hPow _ _ c (hMap (X.gal s) _ _ (hRep (U f)))
  have heq : (Units.map (X.gal s : X.K →* X.K) (U f)) ^ c = U (galU X s f ^ c) := by
    ext
    simp only [U, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [hpow, hGalSl]
    rfl
  rw [heq] at hB
  have hc : Cgr (l ^ n) (U (galU X s f ^ c)) (U (galU X s f ^ c)) := by
    first | rfl | exact ⟨1, by simp⟩ | simp [Cgr]
  have hz := hUniq _ _ _ _ hA hB hc
  rw [map_smul]
  have hsplit : k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) =
      k • (clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
        (c : ℤ_[l]) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) +
      ((k * c) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) -
        k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) := by
    rw [smul_sub, smul_smul]
    abel
  rw [hsplit, map_add (f := _), map_smul, hApi (k * c) k' _ h, add_zero]
  convert smul_zero k using 2

private theorem dvd_iff (l : ℕ) [Fact l.Prime] (n : ℕ) (k k' : ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ k - k' ↔ PadicInt.toZModPow n k = PadicInt.toZModPow n k' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem val_cast {M M' : ℕ} [NeZero M] (h : M' ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod M') = ZMod.castHom h (ZMod M') z := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private noncomputable def dg {M : ℕ} (d : (ZMod M)ˣ) : GL (Fin 2) (ZMod M) :=
  ⟨!![1, 0; 0, (d : ZMod M)], !![1, 0; 0, ((d⁻¹ : (ZMod M)ˣ) : ZMod M)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiTw :
    UpperTheory.V.Z.Kato.Nb.SXiTw := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a s
  have hM0 : M₀ ∣ M := hL.eq ▸ Dvd.intro_left N rfl
  have hlM : l ^ n ∣ M := hL.dl.trans hM0
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨-, -, -, -, -, -, -, hcyc⟩ := sSlD Ω ε X N hN
  have hone : ∀ (K : ℕ) [NeZero K], cycM K (1 : Gal(Ω/ℚ)) = 1 := by
    intro K _
    have h := (hcyc K 1).2.1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hinv : ∀ (K : ℕ) [NeZero K], cycM K s⁻¹ = (cycM K s)⁻¹ := by
    intro K _
    rw [eq_inv_iff_mul_eq_one, ← (hcyc K s⁻¹).2.1 s, inv_mul_cancel, hone]
  set d := cycM M s with hd
  have hcd : ZMod.castHom hM0 (ZMod M₀) ((d⁻¹ : (ZMod M)ˣ) : ZMod M) = cyc M₀ s⁻¹ := by
    rw [(hcyc M₀ s⁻¹).1, ← ((hcyc M s⁻¹).2.2.2.2 M₀ hM0), hinv M]
    rfl
  have hgr : ∀ (z : Row M₀) (m : GL (Fin 2) (ZMod M)),
      gr M₀ s⁻¹ (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) =
        z ᵥ* cD N M₀ ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro z m
    ext i
    fin_cases i
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, val_cast hM0, ← hcd]
      rw [ZMod.cast_mul hM0, ZMod.cast_mul hM0]
      ring
  unfold Xi UpperTheory.Kd.K4.CgF
  intro u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_filter, Finset.sum_filter, map_sum, map_sub, sub_eq_zero]
  conv_rhs => rw [← Fintype.sum_equiv (Equiv.mulRight (dg d⁻¹)) _ _ (fun _ => rfl)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sub_eq_zero, ← map_sub, ← Finset.sum_sub_distrib, map_sum]
  apply Finset.sum_eq_zero
  intro m _
  simp only [Equiv.coe_mulRight]
  have hdet : Matrix.GeneralLinearGroup.det (m * dg d⁻¹) = Matrix.GeneralLinearGroup.det m * d⁻¹ := by
    rw [map_mul]
    congr 1
    ext
    simp [dg, Matrix.det_fin_two, Matrix.GeneralLinearGroup.val_det_apply]
  have hent : ∀ i, ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 ∧
      ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 * ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    intro i
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have hC : Cnd l N g ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) ↔
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    unfold Cnd
    rw [(hent 1).1, (hent 0).1]
  have hP : Matrix.GeneralLinearGroup.det m * d⁻¹ * d = Matrix.GeneralLinearGroup.det m := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  simp only [hdet, hP]
  by_cases h : Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)
  · rw [if_pos h, if_pos ⟨hC.2 h.1, h.2⟩]
    unfold tw
    rw [hgr x m, hgr y m]
    refine term X l n N hN s _ _ _ _ ?_
    rw [dvd_iff]
    simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, (hent 0).1, (hent 0).2]
    have hdl : Units.map (ZMod.castHom hlM (ZMod (l ^ n)) : ZMod M →* ZMod (l ^ n)) d = cycM (l ^ n) s :=
      (hcyc M s).2.2.2.2 (l ^ n) hlM
    have hχ : PadicInt.toZModPow n (((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]ˣ) : ℤ_[l]) =
        ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [(dvd_iff l n _ _).1 (sCycZ Ω l n s).2, map_natCast, ZMod.natCast_zmod_val, ← hdl]
      rfl
    have hc : (((cyc (l ^ n) s).val : ℕ) : ZMod (l ^ n)) = ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [ZMod.natCast_zmod_val, (hcyc (l ^ n) s).1, ← hdl]
      rfl
    simp only [hc, hχ, val_cast hlM, Units.val_mul, mul_inv_rev, inv_inv, map_mul]
    clear hcyc hgr hcd hC hP hdl hone hinv hent hdet h
    set φ := ZMod.castHom hlM (ZMod (l ^ n))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, map_mul, hχ]
    have hdd : φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) * φ (d : ZMod M) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have key : φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) *
        (φ (d : ZMod M) * PadicInt.toZModPow n (u 1)) =
        φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1) := by
      linear_combination (φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)) * hdd
    rw [key]
    ring
  · rw [if_neg h, if_neg (fun h' => h ⟨hC.1 h'.1, h'.2⟩), map_zero, sub_zero, map_zero]
end

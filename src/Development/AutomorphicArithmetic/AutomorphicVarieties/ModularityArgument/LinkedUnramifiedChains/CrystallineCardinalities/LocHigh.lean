module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocLow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.MatrixEntryZeroTwoSubmodule
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.HomBd
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.homBd :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] (ε : D →* ℤ_[l]ˣ) (k : ℕ) (N : Type) [AddCommGroup N] (ρ : Representation ℤ D N) (e : Ok l O k ≃+ N) (χ : D → O) (s₀ : D), (l : O) ≠ 0 → (∀ s x, ρ s (e x) = e (χ s • x)) → χ s₀ - algebraMap ℤ_[l] O (ε s₀) ≠ 0 → (HomMu l k ε ρ).ncard ≤ Nat.card (O ⧸ Ideal.span {χ s₀ - algebraMap ℤ_[l] O (ε s₀)}) := by
  intro l _ O _ _ _ _ _ D _ ε k N _ ρ e χ s₀ hl hρ hc
  classical
  obtain ⟨hfinOk, hfinQ, hkill, -, -, hsm, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfinOk k
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set c := χ s₀ - algebraMap ℤ_[l] O (ε s₀) with hcdef
  haveI : Finite (O ⧸ Ideal.span {c}) := hfinQ c hc
  let I' : Ideal (Ok l O k) := Ideal.span {algebraMap O (Ok l O k) c}
  let π := Ideal.Quotient.mk I'
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have kill : ∀ f ∈ HomMu l k ε ρ, ∀ a : Ok l O k, f (e (c • a)) = 0 := by
    intro f hf a
    have hf' : ∀ s x, f (ρ s x) = PadicInt.toZModPow k (ε s : ℤ_[l]) * f x := hf
    rw [hcdef, sub_smul, map_sub, map_sub, ← hρ, hf', hsm, map_nsmul, map_nsmul, nsmul_eq_mul,
      ZMod.natCast_zmod_val, sub_self]
  have wd : ∀ f ∈ HomMu l k ε ρ, ∀ y y' : Ok l O k, π y = π y' → f (e y) = f (e y') := by
    intro f hf y y' h
    have h' : y - y' ∈ I' := Ideal.Quotient.eq.mp h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h'
    have h2 : y - y' = c • a := by rw [← ha, Algebra.smul_def, mul_comm]
    have h3 := kill f hf a
    rw [← h2, map_sub, map_sub] at h3
    exact sub_eq_zero.mp h3
  let Φ : HomMu l k ε ρ → (Ok l O k ⧸ I' →+ ZMod (l ^ k)) := fun f =>
    { toFun := fun q => f.1 (e (Function.surjInv hπ q))
      map_zero' := by
        rw [wd f.1 f.2 _ 0 (by rw [Function.surjInv_eq hπ, map_zero]), map_zero, map_zero]
      map_add' := by
        intro q q'
        rw [← map_add f.1, ← map_add e]
        apply wd f.1 f.2
        rw [map_add (f := _), Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ] }
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have h1 : ∀ y, f.1 (e y) = g.1 (e y) := by
      intro y
      have := congrArg (fun φ : Ok l O k ⧸ I' →+ ZMod (l ^ k) => φ (π y)) hfg
      change f.1 (e (Function.surjInv hπ (π y))) = g.1 (e (Function.surjInv hπ (π y))) at this
      rw [wd f.1 f.2 y _ (Function.surjInv_eq hπ _).symm, this,
        ← wd g.1 g.2 y _ (Function.surjInv_eq hπ _).symm]
    apply Subtype.ext
    ext x
    have := h1 (e.symm x)
    rwa [AddEquiv.apply_symm_apply] at this
  haveI : Finite (Ok l O k ⧸ I') := Finite.of_surjective π hπ
  have hQk : ∀ q : Ok l O k ⧸ I', l ^ k • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := hπ q
    rw [← map_nsmul, hkill, map_zero]
  obtain ⟨hfin2, hcard2⟩ := dualCard l k (Ok l O k ⧸ I') hQk
  let ψ : O ⧸ Ideal.span {c} →+* Ok l O k ⧸ I' :=
    Ideal.Quotient.lift (Ideal.span {c}) (π.comp (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, map_mul]
      have : π (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by rw [Set.mem_singleton_iff]; rfl))
      rw [this, mul_zero])
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := hπ q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  calc (HomMu l k ε ρ).ncard = Nat.card (HomMu l k ε ρ) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (Ok l O k ⧸ I' →+ ZMod (l ^ k)) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (Ok l O k ⧸ I') := hcard2
    _ ≤ Nat.card (O ⧸ Ideal.span {c}) := Nat.card_le_card_of_surjective ψ hψ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.HomMuLe
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private def ZcA {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    AddSubgroup (D → N) where
  carrier := Zc ρ
  zero_mem' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
    simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add (f := _)]; abel⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
    simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩

private theorem card_ZcA {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    Nat.card (ZcA ρ) = (Zc ρ).ncard := Nat.card_coe_set_eq (Zc ρ)

private theorem idx_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    f.range.index * Nat.card A = Nat.card B * Nat.card f.ker := by
  rw [← AddSubgroup.index_mul_card f.range, ← AddSubgroup.index_mul_card f.ker, AddSubgroup.index_ker]
  ring

private def ZcQ {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N)
    (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) : ZcA ρ →+ ZcA (ρ.quotient N' h) where
  toFun z := ⟨fun s => N'.mkQ (z.1 s), z.2.1.comp N'.mkQ, fun s t => by
    show N'.mkQ (z.1 (s * t)) = N'.mkQ (z.1 s + ρ s (z.1 t))
    rw [z.2.2 s t]⟩
  map_zero' := by ext s; rfl
  map_add' a b := by ext s; rfl

private theorem ker_le {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N)
    (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) (hf : (Zc (ρ.subrepresentation N' h)).Finite) :
    Nat.card (ZcQ ρ N' h).ker ≤ (Zc (ρ.subrepresentation N' h)).ncard := by
  have hm : ∀ z : (ZcQ ρ N' h).ker, ∀ s, z.1.1 s ∈ N' := fun z s => by
    have h1 : ZcQ ρ N' h z.1 = 0 := z.2
    have h2 : N'.mkQ (z.1.1 s) = 0 := congrFun (congrArg Subtype.val h1) s
    exact (Submodule.Quotient.mk_eq_zero N').1 h2
  haveI : Finite (Zc (ρ.subrepresentation N' h)) := hf
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun z => ⟨fun s => ⟨z.1.1 s, hm z s⟩,
    IsLocallyConstant.desc _ (Subtype.val) z.1.2.1 Subtype.val_injective, fun s t => Subtype.ext (z.1.2.2 s t)⟩) ?_
  intro a b hab
  ext s
  exact congrArg Subtype.val (congrFun (congrArg Subtype.val hab) s)

private theorem homMu_le {D N : Type} [Group D] [AddCommGroup N] [Finite N] (l : ℕ) [Fact l.Prime] (k : ℕ) (ε : D →* ℤ_[l]ˣ)
    (ρ : Representation ℤ D N) (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) :
    (HomMu l k ε (ρ.quotient N' h)).ncard ≤ (HomMu l k ε ρ).ncard ∧ 0 < (HomMu l k ε ρ).ncard := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (N →+ ZMod (l ^ k)) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Set.ncard_le_ncard_of_injOn (fun f => f.comp N'.mkQ.toAddMonoidHom) (fun f hf s x => hf s (N'.mkQ x)) ?_, ?_⟩
  · intro a _ b _ hab
    ext x
    obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
    exact DFunLike.congr_fun hab y
  · exact (Set.ncard_pos).2 ⟨0, fun s x => by simp⟩

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.lift :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d k : ℕ), 0 < k → LE l D ε d → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ D N), (∀ x : N, l ^ k • x = 0) → IsOpen (ρ.ker : Set D) → ∀ (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) (C : ℕ), (HomMu l k ε (ρ.subrepresentation N' h)).ncard ≤ C → ∀ z : D → N, IsLocallyConstant z → (∀ s s', z (s * s') - z s - ρ s (z s') ∈ N') → ∃ y ∈ Zc ρ, ∀ s, y s - C.factorial • z s ∈ N' := by
  intro l _ D _ _ _ ε d k hk hLE N _ _ ρ hN hρ N' h C hC z hz hz'
  haveI : Finite (N ⧸ N') := Finite.of_surjective _ N'.mkQ_surjective
  obtain ⟨-, e1⟩ := hLE k hk N ρ hN hρ
  obtain ⟨f2, e2⟩ := hLE k hk N' (ρ.subrepresentation N' h) (fun x => Subtype.ext (hN x.1))
    (Subgroup.isOpen_mono (H₁ := ρ.ker) (fun s hs => by
      have h1 : ρ s = 1 := hs
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ρ s x.1 = x.1
      rw [h1]; rfl) hρ)
  obtain ⟨f3, e3⟩ := hLE k hk (N ⧸ N') (ρ.quotient N' h) (fun x => by
      obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
      rw [← map_nsmul, hN, map_zero])
    (Subgroup.isOpen_mono (H₁ := ρ.ker) (fun s hs => by
      have h1 : ρ s = 1 := hs
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
      show N'.mkQ (ρ s y) = N'.mkQ y
      rw [h1]; rfl) hρ)
  have e4 := idx_mul (ZcQ ρ N' h)
  rw [card_ZcA, card_ZcA, e1, e3] at e4
  have e5 := ker_le ρ N' h f2
  rw [e2] at e5
  obtain ⟨e6, e7⟩ := homMu_le l k ε ρ N' h
  have e8 : Nat.card N = Nat.card N' * Nat.card (N ⧸ N') := Submodule.card_eq_card_quotient_mul_card N'
  have hpos : 0 < Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard := Nat.mul_pos (pow_pos Nat.card_pos _) e7
  have hle : (ZcQ ρ N' h).range.index ≤ C := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e4]
    calc _ ≤ Nat.card (N ⧸ N') ^ (1 + d) * (HomMu l k ε ρ).ncard * (Nat.card N' ^ (1 + d) * C) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e6) (e5.trans (Nat.mul_le_mul_left _ hC))
      _ = _ := by rw [e8, mul_pow]; ring
  haveI : Finite (ZcA (ρ.quotient N' h)) := f3
  have hne : (ZcQ ρ N' h).range.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hne) hle
  let w : ZcA (ρ.quotient N' h) := ⟨fun s => N'.mkQ (z s), hz.comp N'.mkQ, fun s t => by
    show N'.mkQ (z (s * t)) = N'.mkQ (z s + ρ s (z t))
    refine (Submodule.Quotient.eq N').2 ?_
    rw [← sub_sub]; exact hz' s t⟩
  have hw : C.factorial • w ∈ (ZcQ ρ N' h).range := by
    rw [hc, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_index_mem _ w) c
  obtain ⟨y, hy⟩ := hw
  refine ⟨y.1, y.2, fun s => (Submodule.Quotient.eq N').1 ?_⟩
  have h2 : N'.mkQ (y.1 s) = C.factorial • N'.mkQ (z s) := congrFun (congrArg Subtype.val hy) s
  rw [← map_nsmul] at h2
  exact h2
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.YEx

private def matrixEntryZeroTwoSubmodule (R : Type) [CommRing R] : Submodule ℤ (Matrix (Fin 3) (Fin 3) R) where
  carrier := {X | ∀ a b, ¬ (a = 0 ∧ b = 2) → X a b = 0}
  add_mem' := fun hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

private theorem single_mem {R : Type} [CommRing R] (x : R) : Matrix.single (0 : Fin 3) (2 : Fin 3) x ∈ matrixEntryZeroTwoSubmodule R := by
  intro a b h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨rfl, rfl⟩

private theorem eq_single {R : Type} [CommRing R] {X : Matrix (Fin 3) (Fin 3) R} (h : X ∈ matrixEntryZeroTwoSubmodule R) :
    X = Matrix.single (0 : Fin 3) (2 : Fin 3) (X 0 2) := by
  ext a b
  rw [Matrix.single_apply]
  by_cases hab : a = 0 ∧ b = 2
  · obtain ⟨rfl, rfl⟩ := hab
    simp
  · rw [if_neg (fun h' => hab ⟨h'.1.symm, h'.2.symm⟩)]
    exact h a b hab

private def e02 (R : Type) [CommRing R] : R ≃+ matrixEntryZeroTwoSubmodule R where
  toFun x := ⟨Matrix.single 0 2 x, single_mem x⟩
  invFun X := X.1 0 2
  left_inv x := by simp
  right_inv X := Subtype.ext (eq_single X.2).symm
  map_add' x y := Subtype.ext (by simp [Matrix.single_add])

private def zM {R : Type} [CommRing R] (i : Fin 2) (u b : R) : Matrix (Fin 3) (Fin 3) R :=
  if i = 0 then !![u, b, 0; 0, 0, 0; 0, 0, 0] else !![0, 0, 0; 0, 0, b; 0, 0, -u]

private theorem zM_upT {R : Type} [CommRing R] (i : Fin 2) (u b : R) : UpT (zM i u b) := by
  intro a c h
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h ⊢

private theorem zM_diag {R : Type} [CommRing R] (i : Fin 2) (b : R) (j : Fin 3) : zM i 0 b j j = 0 := by
  fin_cases i <;> fin_cases j <;> simp [zM]

private theorem zM_diff {R : Type} [CommRing R] (i : Fin 2) (u b : R) :
    zM i u b i.castSucc i.castSucc - zM i u b i.succ i.succ = u := by
  fin_cases i <;> simp [zM]

private theorem zM_coc {O R : Type} [CommRing O] [CommRing R] [Module O R] (i : Fin 2) (u b u' b' b'' : R)
    (Y : Matrix (Fin 3) (Fin 3) R) (p q : Fin 2 → O) (h1 : UpT Y) (h2 : ∀ j, Y j j = zM i u' b' j j)
    (h3 : ∀ j : Fin 2, Y j.castSucc j.succ = p j • zM i u' b' j.castSucc j.succ -
      q j • (zM i u' b' j.castSucc j.castSucc - zM i u' b' j.succ j.succ))
    (h4 : b'' = b + p i • b' - q i • u') : zM i (u + u') b'' - zM i u b - Y ∈ matrixEntryZeroTwoSubmodule R := by
  subst h4
  intro a c h
  have d0 := h2 0
  have d1 := h2 1
  have d2 := h2 2
  have s0 := h3 0
  have s1 := h3 1
  have l10 := h1 1 0 (by decide)
  have l20 := h1 2 0 (by decide)
  have l21 := h1 2 1 (by decide)
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h d0 d1 d2 s0 s1 ⊢ <;> simp [d0, d1, d2, s0, s1, l10, l20, l21] <;> abel

private theorem natCast_ne (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (hl : (l : O) ≠ 0) (n : ℕ) : n ≠ 0 → (n : O) ≠ 0 := by
  intro hn
  obtain ⟨p, hp⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O p with hpp | rfl
  · exfalso
    have h1 : ((p : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), CharP.cast_eq_zero O p, map_zero]
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h1
    have hlp : l = p := (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).mp h1
    subst hlp
    exact hl (CharP.cast_eq_zero O l)
  · haveI : CharZero O := CharP.charP_to_charZero O
    exact_mod_cast hn

end UpperTheory.V.Z.J.YEx

open UpperTheory.V.Z.J.YEx in
theorem UpperTheory.V.Z.J.yEx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∃ c : O, c ≠ 0 ∧ ∀ k, 0 < k → ∃ y ∈ ZF (l := l) I k t, ∃ s, y s i.castSucc i.castSucc - y s i.succ i.succ = Ideal.Quotient.mk _ c := by
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hGen hT i hU
  have hinv := (cjFacts l O D t 0 hl hT).2.1
  obtain ⟨hdiag, u, β, hu, hβ, hadd, hI, ⟨s0, hs0⟩, hβc⟩ := hU
  obtain ⟨s1, hs1⟩ := hT.dist
  have hχne : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
      - algebraMap ℤ_[l] O (ε s1) ≠ 0 := by
    have h22 := (hinv s1).2 2
    have hε : algebraMap ℤ_[l] O (ε s1) ≠ 0 := ((ε s1).isUnit.map (algebraMap ℤ_[l] O)).ne_zero
    have hi22 : (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at h22
      exact zero_ne_one h22
    fin_cases i
    · have hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
          = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 := hdiag s1
      have key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
          - algebraMap ℤ_[l] O (ε s1) = algebraMap ℤ_[l] O (ε s1) * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
            * ((t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 - (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2) := by
        linear_combination (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd
          + algebraMap ℤ_[l] O (ε s1) * h22
      rw [key]
      exact mul_ne_zero (mul_ne_zero hε hi22) (hs1 1 2 (by decide)).ne_zero
    · have hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1
          = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2 := hdiag s1
      have key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
          - algebraMap ℤ_[l] O (ε s1) = (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
            * ((t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 - (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1) := by
        linear_combination (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd
          + algebraMap ℤ_[l] O (ε s1) * h22
      rw [key]
      exact mul_ne_zero hi22 (hs1 0 1 (by decide)).ne_zero
  refine ⟨((Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
      * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)})).factorial : O) * u s0,
    mul_ne_zero (natCast_ne l O hl _ (Nat.factorial_ne_zero _)) hs0, ?_⟩
  generalize hC : Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
      * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)}) = C
  intro k hk
  obtain ⟨⟨ρ, hρ, hρopen⟩, -, hcj, hsingle, -⟩ := cjFacts l O D t k hl hT
  obtain ⟨hfin, -, hlk, -, hpow, -, -⟩ := okFin l O hl
  haveI := hfin k
  obtain ⟨Nk, hNk⟩ := hpow k
  have hmk : ∀ f : D → O, AdicCont (maximalIdeal O) f →
      IsLocallyConstant (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s)) := by
    intro f hf
    have e : (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s))
        = (Ideal.Quotient.factor hNk) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal O ^ Nk) (f g)) := by
      funext s
      simp [Ideal.Quotient.factor_mk]
    rw [e]
    exact (hf Nk).comp _
  have hN : ∀ s, matrixEntryZeroTwoSubmodule (Ok l O k) ≤ Submodule.comap (ρ s) (matrixEntryZeroTwoSubmodule (Ok l O k)) := by
    intro s X hX
    rw [Submodule.mem_comap, hρ, eq_single hX, hsingle]
    exact single_mem _
  have hbound : (HomMu l k ε (ρ.subrepresentation (matrixEntryZeroTwoSubmodule (Ok l O k)) hN)).ncard ≤ C := by
    rw [← hC]
    refine homBd l O D ε k _ _ (e02 (Ok l O k))
      (fun s => (t s : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2)
      s1 hl ?_ hχne
    intro s x
    apply Subtype.ext
    show ρ s (Matrix.single 0 2 x) = Matrix.single 0 2 _
    rw [hρ, hsingle]
  have hzlc : IsLocallyConstant (fun s => zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s))) :=
    IsLocallyConstant.comp₂ (hmk u hu) (hmk β hβ) _
  have hzcoc : ∀ s s', zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u (s * s')))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β (s * s')))
      - zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s))
      - ρ s (zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s'))
          (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s'))) ∈ matrixEntryZeroTwoSubmodule (Ok l O k) := by
    intro s s'
    rw [hρ, hadd, map_add (f := _)]
    have hz' := hcj s _ (zM_upT i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s'))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s')))
    refine zM_coc i _ _ _ _ _ _
      (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.castSucc
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ)
      (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.succ
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ)
      hz'.1 hz'.2.1 hz'.2.2 ?_
    have hp : (t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.castSucc
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i.succ i.succ = algebraMap ℤ_[l] O (ε s) := by
      rw [hdiag s, mul_assoc, (hinv s).2, mul_one]
    beta_reduce
    rw [hp, hβc, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    simp only [map_add (f := _), map_sub, map_mul]
  obtain ⟨y, ⟨hylc, hycoc⟩, hy⟩ := lift l D ε d k hk hLE (Matrix (Fin 3) (Fin 3) (Ok l O k)) ρ
    (fun X => by ext a b; simp [hlk]) hρopen (matrixEntryZeroTwoSubmodule (Ok l O k)) hN C hbound _ hzlc hzcoc
  have hyent : ∀ s (a b : Fin 3), ¬ (a = 0 ∧ b = 2) → y s a b = C.factorial •
      zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s)) a b := by
    intro s a b hab
    have h := (hy s : ∀ a b : Fin 3, ¬ (a = 0 ∧ b = 2) → _) a b hab
    simp only [Matrix.sub_apply, Matrix.smul_apply] at h
    exact sub_eq_zero.mp h
  have hnd : ∀ j : Fin 3, ¬ (j = 0 ∧ j = 2) := by decide
  refine ⟨y, ?_, s0, ?_⟩
  · show IsLocallyConstant y ∧ (∀ s s', y (s * s') = y s + cj k t s (y s')) ∧ (∀ s, UpT (y s)) ∧
      ∀ s ∈ I, ∀ j : Fin 3, y s j j = 0
    refine ⟨hylc, fun s s' => by rw [hycoc, hρ], ?_, ?_⟩
    · intro s a b hab
      rw [hyent s a b ?_, zM_upT i _ _ a b hab, smul_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (by decide)
    · intro s hs j
      rw [hyent s j j (hnd j), hI s hs, map_zero, zM_diag, smul_zero]
  · rw [hyent s0 _ _ (hnd _), hyent s0 _ _ (hnd _), ← smul_sub, zM_diff, nsmul_eq_mul, map_mul, map_natCast]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LowerTriangularAbsorbsTorsion
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem lower_triangular_absorbs_torsion (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D)
    (ε : D →* ℤ_[l]ˣ) (d k : ℕ) (hk : 0 < k) (hLE : LE l D ε d) (hG : GenI l I d)
    (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N] [Finite N]
    (hA : ∀ x : A, l ^ k • x = 0) (hN : ∀ x : N, l ^ k • x = 0) (ρ : Representation ℤ D N)
    (hρ : IsOpen (ρ.ker : Set D)) (hc : Nat.card A ^ 5 ≤ Nat.card N) (e : N →+ A) (he : Function.Surjective e)
    (hε : ∀ s x, e (ρ s x) = (PadicInt.toZModPow k (ε s : ℤ_[l])).val • e x)
    (p : Fin 2 → N →+ A) (hp : ∀ j s x, p j (ρ s x) = p j x) :
    (Zc ρ).Finite ∧ Nat.card A ^ (6 + 3 * d) ≤ {z | z ∈ Zc ρ ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard := by
  classical
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hZfin, hZcard⟩ := hLE k hk N ρ hN hρ
  refine ⟨hZfin, ?_⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  obtain ⟨hdA, hcA⟩ := dualCard l k A hA
  obtain ⟨hdN, -⟩ := dualCard l k N hN
  haveI := hdA
  haveI := hdN
  have hHom : Nat.card A ≤ (HomMu l k ε ρ).ncard := by
    rw [← hcA, ← Set.ncard_univ]
    refine Set.ncard_le_ncard_of_injOn (fun φ => φ.comp e) ?_ ?_ (Set.toFinite _)
    · intro φ _ s x
      show φ (e (ρ s x)) = _ * φ (e x)
      rw [hε, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    · intro φ _ ψ _ h
      exact (AddMonoidHom.cancel_right he).1 h
  have hbig : Nat.card A ^ (6 + 5 * d) ≤ (Zc ρ).ncard := by
    rw [hZcard]
    calc Nat.card A ^ (6 + 5 * d) = (Nat.card A ^ 5) ^ (1 + d) * Nat.card A := by
          rw [← pow_mul, ← pow_succ]; congr 1; ring
      _ ≤ Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc _) hHom
  let Z : AddSubgroup (D → N) :=
    { carrier := Zc ρ
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
        simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add (f := _)]; abel⟩
      zero_mem' := h0
      neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
        simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩ }
  haveI : Finite Z := hZfin.to_subtype
  have hpZ : ∀ z ∈ Z, IsLocallyConstant z ∧
      ∀ (j : Fin 2) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s') := by
    intro z hz
    have hz' : z ∈ Zc ρ := hz
    refine ⟨hz'.1, fun j s s' => ?_⟩
    rw [hz'.2 s s', map_add (f := _), hp]
  have hcut := wtCut l D I d k 2 A N hG hA Z inferInstance p hpZ
  have hZc : Nat.card Z = (Zc ρ).ncard := Nat.card_coe_set_eq (Zc ρ)
  have hApos : 0 < Nat.card A ^ (2 * d) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hApos
  calc Nat.card A ^ (6 + 3 * d) * Nat.card A ^ (2 * d) = Nat.card A ^ (6 + 5 * d) := by
        rw [← pow_add]; congr 1; ring
    _ ≤ (Zc ρ).ncard := hbig
    _ = Nat.card Z := hZc.symm
    _ ≤ _ := hcut

private def b0 (A : Type) [AddCommGroup A] (i : Fin 2) : Submodule ℤ (Matrix (Fin 3) (Fin 3) A) where
  carrier := {X | UpT X ∧ X i.castSucc i.castSucc = X i.succ i.succ}
  zero_mem' := ⟨fun _ _ _ => rfl, rfl⟩
  add_mem' := fun {a b} ha hb => ⟨fun x y h => by simp [ha.1 x y h, hb.1 x y h], by simp [ha.2, hb.2]⟩
  smul_mem' := fun c a ha => ⟨fun x y h => by simp [ha.1 x y h], by simp [ha.2]⟩

private theorem card_borel_torsion_lower_bound (A : Type) [AddCommGroup A] [Finite A] (i : Fin 2) : Nat.card A ^ 5 ≤ Nat.card (b0 A i) := by
  classical
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hcc : i.castSucc ≤ i.castSucc ∧ (i.castSucc, i.castSucc) ≠ (i.succ, i.succ) :=
    ⟨le_rfl, fun h => hlt.ne (congrArg Prod.fst h)⟩
  let F : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → Matrix (Fin 3) (Fin 3) A :=
    fun g a b => if h : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) then g ⟨(a, b), h⟩
      else if (a, b) = (i.succ, i.succ) then g ⟨(i.castSucc, i.castSucc), hcc⟩ else 0
  have hF : ∀ g, F g ∈ b0 A i := by
    intro g
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 : ¬ (a ≤ b ∧ (a, b) ≠ (i.succ, i.succ)) := fun h => absurd h.1 (not_le.mpr hab)
      have h2 : (a, b) ≠ (i.succ, i.succ) := by
        intro h
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2] at hab
        exact lt_irrefl _ hab
      simp only [F, dif_neg h1, if_neg h2]
    · have h3 : ¬ (i.succ ≤ i.succ ∧ (i.succ, i.succ) ≠ (i.succ, i.succ)) := fun h => h.2 rfl
      simp only [F, dif_pos hcc, dif_neg h3]
      simp
  let f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → b0 A i := fun g => ⟨F g, hF g⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    funext ⟨⟨a, b⟩, hp⟩
    have hp' : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) := hp
    have := congrArg (fun x : b0 A i => (x : Matrix (Fin 3) (Fin 3) A) a b) hgg
    simp only [f, F, dif_pos hp'] at this
    exact this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at h1
  have h5 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} = 5 := by
    rw [Nat.card_eq_fintype_card]; fin_cases i <;> decide
  rwa [h5] at h1

private def ent (A : Type) [AddCommGroup A] (i : Fin 2) (a b : Fin 3) : b0 A i →+ A where
  toFun X := X.1 a b
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem ent_surj (A : Type) [AddCommGroup A] (i : Fin 2) : Function.Surjective (ent A i i.castSucc i.succ) := by
  intro a
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  refine ⟨⟨Matrix.single i.castSucc i.succ a, ?_, ?_⟩, ?_⟩
  · intro x y h
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.mpr hlt.le)
  · simp [Matrix.single_apply, hlt.ne, hlt.ne']
  · show Matrix.single i.castSucc i.succ a i.castSucc i.succ = a
    simp

theorem UpperTheory.V.Z.J.low0 :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∀ k, 0 < k → Nat.card (Ok l O k) ^ (6 + 3 * d) ≤ {z | z ∈ ZF (l := l) I k t ∧ ∀ s, z s i.castSucc i.castSucc = z s i.succ i.succ}.ncard := by
  classical
  have key : ∀ (R : Type) [AddCommGroup R] (i : Fin 2) (M : Matrix (Fin 3) (Fin 3) R),
      M i.castSucc i.castSucc = M i.succ i.succ →
      (∀ j : Fin 2, M (if i = 0 then j.succ else j.castSucc) (if i = 0 then j.succ else j.castSucc) = 0) →
      ∀ a, M a a = 0 := by
    intro R _ i M h1 h2 a
    have h20 := h2 0
    have h21 := h2 1
    fin_cases i <;> fin_cases a <;> simp_all
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI hT i hU k hk
  obtain ⟨hfin, -, hkill, -, -, hsmul, -⟩ := okFin l O hl
  haveI := hfin k
  obtain ⟨⟨ρ, hρ, hker⟩, hinv, hcj, -⟩ := cjFacts l O D t k hl hT
  have hAm : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0 := fun x => by
    ext a b; simp [hkill]
  have hN : ∀ x : b0 (Ok l O k) i, l ^ k • x = 0 := fun x =>
    Subtype.ext (by rw [Submodule.coe_smul_of_tower]; exact hAm x.1)
  have hmem : ∀ s (x : b0 (Ok l O k) i), ρ s x.1 ∈ b0 (Ok l O k) i := fun s x => by
    obtain ⟨hx1, hx2⟩ := x.2
    refine ⟨?_, ?_⟩
    · rw [hρ]; exact (hcj s x.1 hx1).1
    · rw [hρ, (hcj s x.1 hx1).2.1, (hcj s x.1 hx1).2.1]; exact hx2
  let f : D → (b0 (Ok l O k) i →+ b0 (Ok l O k) i) := fun s =>
    { toFun := fun x => ⟨ρ s x.1, hmem s x⟩
      map_zero' := Subtype.ext (map_zero (ρ s))
      map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }
  let q : Fin 2 → Fin 3 := fun j => if i = 0 then j.succ else j.castSucc
  let p : Fin 2 → (b0 (Ok l O k) i →+ Ok l O k) := fun j => ent (Ok l O k) i (q j) (q j)
  refine le_trans (lower_triangular_absorbs_torsion l D I ε d k hk hLE hI (Ok l O k) (b0 (Ok l O k) i) (hkill k) hN
      { toFun := fun s => (f s).toIntLinearMap
        map_one' := LinearMap.ext fun x => Subtype.ext (by
          show ρ 1 x.1 = x.1
          rw [map_one]; rfl)
        map_mul' := fun s s' => LinearMap.ext fun x => Subtype.ext (by
          show ρ (s * s') x.1 = ρ s (ρ s' x.1)
          rw [map_mul]; rfl) }
      ?_ (card_borel_torsion_lower_bound _ i) (ent _ i i.castSucc i.succ) (ent_surj _ i) ?_ p ?_).2 ?_
  · refine Subgroup.isOpen_mono (fun s hs => ?_) hker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact LinearMap.ext fun x => Subtype.ext (by
      show ρ s x.1 = x.1
      rw [hs]; rfl)
  · intro s x
    obtain ⟨hx1, hx2⟩ := x.2
    show ρ s x.1 i.castSucc i.succ = _ • x.1 i.castSucc i.succ
    rw [hρ, (hcj s x.1 hx1).2.2 i, hx2, sub_self, smul_zero, sub_zero, ← hsmul k,
      hU.1 s, mul_assoc, (hinv s).2 i.succ, mul_one]
  · intro j s x
    show ρ s x.1 (q j) (q j) = x.1 (q j) (q j)
    rw [hρ, (hcj s x.1 x.2.1).2.1]
  · refine Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ ?_
    · rintro z ⟨hz, hI0⟩
      refine ⟨⟨hz.1.comp _, fun s s' => ?_, fun s => (z s).2.1, fun s hs a => ?_⟩, fun s => (z s).2.2⟩
      · show (z (s * s')).1 = (z s).1 + cj k t s (z s').1
        rw [hz.2 s s', ← hρ]; rfl
      · exact key _ i (z s).1 (z s).2.2 (fun j => hI0 j s hs) a
    · intro z _ z' _ h
      funext s; exact Subtype.ext (congrFun h s)
    · exact (hLE k hk _ ρ hAm hker).1.subset (fun z hz => ⟨hz.1.1, fun s s' => by rw [hz.1.2.1, hρ]⟩)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {D : Type} [Group D] [TopologicalSpace D]

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.locHigh :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∃ C : ℕ, ∀ k, 0 < k → Nat.card (Ok l O k) ^ (7 + 3 * d) ≤ C * (ZF (l := l) I k t).ncard := by
  classical
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hG hT i hU
  obtain ⟨c, hc0, hy⟩ := yEx l O D I ε d t hl hLE hG hT i hU
  have hOk := okFin l O hl
  haveI : Finite (O ⧸ Ideal.span {c}) := hOk.2.1 c hc0
  refine ⟨Nat.card (O ⧸ Ideal.span {c}), fun k hk => ?_⟩
  haveI : Finite (Ok l O k) := hOk.1 k
  obtain ⟨hZfin, -⟩ := locLow l O D I ε d t hl hLE hG hT k hk
  have hW := low0 l O D I ε d t hl hLE hG hT i hU k hk
  obtain ⟨y, hyZ, s0, hys⟩ := hy k hk
  set mc : Ok l O k := Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c with hmc
  have hmem : ∀ w ∈ ZF (l := l) I k t, ∀ a : Ok l O k, w + a • y ∈ ZF (l := l) I k t := by
    intro w hw a
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hyZ
    refine ⟨hw1.add (hy1.comp (fun x => a • x)), ?_, ?_, ?_⟩
    · intro s s'
      simp only [Pi.add_apply, Pi.smul_apply, hw2 s s', hy2 s s', cj, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_add]
      abel
    · intro s p q hpq
      simp [hw3 s p q hpq, hy3 s p q hpq]
    · intro s hs p
      simp [hw4 s hs p, hy4 s hs p]
  set W := {z | z ∈ ZF (l := l) I k t ∧ ∀ s, z s i.castSucc i.castSucc = z s i.succ i.succ} with hWdef
  let J : Ideal (Ok l O k) := Ideal.span {mc}
  let g : Ok l O k → Ok l O k := fun b => if h : ∃ a, a * mc = b then h.choose else 0
  have hg : ∀ b ∈ (J : Set (Ok l O k)), g b * mc = b := by
    intro b hb
    have h : ∃ a, a * mc = b := Ideal.mem_span_singleton'.mp hb
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hcount : (W ×ˢ (J : Set (Ok l O k))).ncard ≤ (ZF (l := l) I k t).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p => p.1 + g p.2 • y) ?_ ?_ hZfin
    · rintro ⟨w, b⟩ ⟨hw, -⟩
      exact hmem w hw.1 _
    · rintro ⟨w, b⟩ ⟨hw, hb⟩ ⟨w', b'⟩ ⟨hw', hb'⟩ h
      dsimp only at h hw hb hw' hb'
      have h1 := congrFun (congrFun (congrFun h s0) i.castSucc) i.castSucc
      have h2 := congrFun (congrFun (congrFun h s0) i.succ) i.succ
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
      have hwa : w s0 i.castSucc i.castSucc = w s0 i.succ i.succ := hw.2 s0
      have hwb : w' s0 i.castSucc i.castSucc = w' s0 i.succ i.succ := hw'.2 s0
      have hbb : b = b' := by
        linear_combination -(hg b hb) + hg b' hb' - (g b - g b') * hys + h1 - h2 - hwa + hwb
      subst hbb
      have : w = w' := add_right_cancel h
      simp [this]
  have hJ : Nat.card (Ok l O k) ≤ Nat.card (O ⧸ Ideal.span {c}) * (J : Set (Ok l O k)).ncard := by
    have h1 : Nat.card (Ok l O k) = Nat.card J * Nat.card (Ok l O k ⧸ J) :=
      Submodule.card_eq_card_quotient_mul_card J
    have h2 : Nat.card (Ok l O k ⧸ J) ≤ Nat.card (O ⧸ Ideal.span {c}) := by
      let φ : O →+* Ok l O k ⧸ J := (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk _)
      have hφ : ∀ a ∈ Ideal.span {c}, φ a = 0 := by
        intro a ha
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, show φ c = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
          mul_zero]
      apply Nat.card_le_card_of_surjective (Ideal.Quotient.lift _ φ hφ)
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    rw [h1, mul_comm, ← Nat.card_coe_set_eq]
    exact Nat.mul_le_mul_right _ h2
  calc Nat.card (Ok l O k) ^ (7 + 3 * d)
      = Nat.card (Ok l O k) ^ (6 + 3 * d) * Nat.card (Ok l O k) := by ring
    _ ≤ W.ncard * (Nat.card (O ⧸ Ideal.span {c}) * (J : Set (Ok l O k)).ncard) := Nat.mul_le_mul hW hJ
    _ = Nat.card (O ⧸ Ideal.span {c}) * (W ×ˢ (J : Set (Ok l O k))).ncard := by rw [Set.ncard_prod]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcount

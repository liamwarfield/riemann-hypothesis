module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres
noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Coord

variable {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
  (r : G →* GG (m := 3) (R := R)) (W : WPres O ℤ R)

def IsCoord (s : W.σ) : Prop :=
  ∃ g a b, W.wt s = wt6 a - wt6 b ∧ W.z s = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)

def EntHomog : Prop := ∀ g a b, emb (r g) a b ∈ W.part (wt6 a - wt6 b)

end Coord

def boxDef (j : ℤ) : ℕ := if |j| ≤ 1 then 1 else 0

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H]

def IsLocPres {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (WB : WPres O ℤ (U.R ⧸ I)) :
    Prop :=
  (∀ s, IsCoord η Ψ (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB s) ∧ EntHomog (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB

variable {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R}

def BoxPres (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) : Prop :=
  ∃ (W : WPres O ℤ B.R) (i : (U.R ⧸ I) →ₐ[O] B.R) (τ κ : Type) (_ : Fintype τ) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ),
    IsRelPres WB i W e f wf ∧ push (i.comp (Ideal.Quotient.mkₐ O I)) U.r.hom = B.r.hom.comp ι ∧
    (∀ t, IsCoord η Ψ B.r.hom W (e (.inr t))) ∧ EntHomog B.r.hom W ∧
    ∀ j, Nat.card {u // wf u = j} = Nat.card {t // W.wt (e (.inr t)) = j} + boxDef j

end UpperTheory.V.U3
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtShape
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem zmat_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (c g₁ : G)
    (r : G →* GG (m := 3) (R := R)) (i j : Fin 3) : zmat c g₁ ((GG.map f).comp r) i j = f (zmat c g₁ r i j) := by
  simp only [zmat, Matrix.sub_apply, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, map_sub]

private theorem normalised_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) {c g₁ : G}
    {r : G →* GG (m := 3) (R := R)} (h : Normalised c g₁ r) : Normalised c g₁ ((GG.map f).comp r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [MonoidHom.comp_apply, GG.map_mat, h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  · rw [zmat_map, h.z12, map_zero]
  · rw [zmat_map, h.z21, map_zero]

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g : 1
  refine SemidirectProduct.ext ?_ ?_
  · ext i j
    simp [r0, GG.map, tor_val, Matrix.diagonal_apply]
    split_ifs
    · simp only [← map_zpow, ← map_pow, Units.coe_map]
      rfl
    · exact map_zero f
  · simp [r0, GG.map]

private theorem zeta_sub_mem {O Γ R : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (c g₁ : Γ) :
    zeta c g₁ r.hom - algebraMap O R (zeta c g₁ (r0 η Ψ)) ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O R, map_sub, sub_eq_zero]
  have h1 : (res O R) (zeta c g₁ r.hom) =
      zeta c g₁ ((GG.map (res O R : R →+* ResidueField O)).comp r.hom) :=
    (zmat_map (res O R : R →+* ResidueField O) c g₁ r.hom 0 0).symm
  have h2 : (GG.map (res O R : R →+* ResidueField O)).comp r.hom = r0 η (barChar O Ψ) := by
    ext1 g
    exact r.red g
  have h3 : r0 η (barChar O Ψ) = (GG.map (residue O)).comp (r0 η Ψ) := by
    rw [map_reducible_three_dim]
    rfl
  rw [h1, h2, h3]
  show zmat c g₁ ((GG.map (residue O)).comp (r0 η Ψ)) 0 0 = _
  rw [zmat_map]
  simp [zeta]

private theorem norm_coe_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hint : IsIntegral ℤ_[l] (x : PadicAlgCl l) := by
    have hx : IsIntegral ℤ_[l] x := Algebra.IsIntegral.isIntegral x
    exact hx.map c.O.val
  obtain ⟨p, hmon, hp⟩ := hint
  by_contra hgt
  push_neg at hgt
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hp
  have hcoef : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l)
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖(x : PadicAlgCl l)‖ ^ i := by
    intro i _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one _
    calc _ ≤ 1 * ‖(x : PadicAlgCl l)‖ ^ i := by gcongr
      _ = _ := one_mul _
  have hlt : ‖∑ i ∈ Finset.range p.natDegree, Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l))
      (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ <
      ‖(x : PadicAlgCl l)‖ ^ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
    · rw [hn]
      simp
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hn.ne') (fun i => Polynomial.eval₂
          (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i))
      exact lt_of_le_of_lt (hle.trans (hcoef i hi)) (pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi))
  have heq := eq_neg_of_add_eq_zero_left hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  linarith

theorem UpperTheory.V.U3.twoPt_shape :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ}
      (S : SRing (N := N) (hι := hι) (U := U) (I := I) (c := cc) (g₁ := g₁)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, TwoPt (η := η) S.r.hom f →
        (TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → MatIso η.ker (mats (push f S.r.hom)) (mats (push f' S.r.hom)) →
          ∃ t : (PadicAlgCl l)ˣ, push f' S.r.hom = conjBy (tor (R := PadicAlgCl l) t) (push f S.r.hom) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S hl2 hmk f htwo
  have hid : (GLift.map (AlgHom.id c.O S.R) S.r).hom = S.r.hom := by
    ext g : 1
    refine SemidirectProduct.ext ?_ ?_
    · ext i j
      simp [GLift.map, GG.map]
    · simp [GLift.map, GG.map]
  have hN : Normalised cc g₁ S.r.hom := by
    have h := ((S.rep S.R).1 (AlgHom.id c.O S.R)).1
    rwa [hid] at h
  have hmult : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, HasMult η (push g S.r.hom) := by
    intro g x
    simpa [push, GG.map] using S.r.hasMult x
  have hnorm_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, Normalised cc g₁ (push g S.r.hom) :=
    fun g => normalised_map (g : S.R →+* PadicAlgCl l) hN
  have hzeta_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l,
      zeta cc g₁ (push g S.r.hom) = g (zeta cc g₁ S.r.hom) :=
    fun g => zmat_map (g : S.R →+* PadicAlgCl l) cc g₁ S.r.hom 0 0
  obtain ⟨_, hz0u⟩ := zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ cc g₁ hmk
  have hmem := zeta_sub_mem S.r cc g₁
  have ha : ‖algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ = 1 := by
    obtain ⟨u, hu⟩ := hz0u
    have h1 := norm_coe_coefO_le_one c (zeta cc g₁ (r0 η Ψ))
    have h2 := norm_coe_coefO_le_one c (↑u⁻¹ : c.O)
    have hprod : algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) *
        algebraMap c.O (PadicAlgCl l) (↑u⁻¹ : c.O) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hn := congrArg norm hprod
    rw [norm_mul, norm_one] at hn
    change ‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ = 1 at hn
    change ‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ = 1
    have key := mul_le_mul_of_nonneg_left h2 (norm_nonneg ((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l))
    rw [mul_one] at key
    exact le_antisymm h1 (by linarith)
  have hdec : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g →
      ‖zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ < 1 := by
    intro g hg
    rw [hzeta_g, ← AlgHom.commutes g, ← map_sub]
    exact hg _ hmem
  have hne0 : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → zeta cc g₁ (push g S.r.hom) ≠ 0 := by
    intro g hg h0
    have h := hdec g hg
    rw [h0, zero_sub, norm_neg, ha] at h
    exact lt_irrefl _ h
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have h2e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [Nat.cast_ofNat, map_ofNat]
    rw [h2e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl2
  have hnn : ∀ g g' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → IsLocPt g' →
      zeta cc g₁ (push g' S.r.hom) ≠ -zeta cc g₁ (push g S.r.hom) := by
    intro g g' hg hg' heq
    have e1 := hdec g hg
    have e2 := hdec g' hg'
    have hsum : (2 : PadicAlgCl l) * algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) =
        -((zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))) +
          (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))) := by
      rw [heq]
      ring
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))
      (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))
    have hn := congrArg norm hsum
    rw [norm_neg, norm_mul, h2, ha, one_mul] at hn
    have hm := max_lt e1 e2
    linarith
  have hf := htwo.1
  have hcases := shape_cases η (push f S.r.hom) cc g₁ two_ne_zero (hmult f) hmk.ηc hmk.ηg
    (hnorm_g f) (hne0 f hf)
  have htype : TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom) := by
    rcases hcases with h | h | h | h
    · exact Or.inl h
    · exact absurd h htwo.2.1
    · exact absurd h htwo.2.2
    · exact Or.inr h
  refine ⟨htype, ?_⟩
  intro f' hf' hiso
  exact conjBy_tor_of_iso η (push f S.r.hom) (push f' S.r.hom) cc g₁ two_ne_zero (hmult f) (hmult f')
    hmk.ηc hmk.ηg (hnorm_g f) (hnorm_g f') (hne0 f hf) (hne0 f' hf') (hnn f f' hf hf') htype hiso
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivQuot
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.U3

section Quot

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

private theorem glift_map_map {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R']
    [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R) (f : R →ₐ[O] R')
    (f' : R' →ₐ[O] R'') : (r.map f).map f' = r.map (f'.comp f) := GLift.ext rfl

private theorem univ_quot {P Q : GCond O η Ψ} (V : Univ P) (J : Ideal V.R)
    (hQP : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R), Q R r → P R r)
    (hJ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (f : V.R →ₐ[O] R),
      Q R (V.r.map f) ↔ J ≤ RingHom.ker f)
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : Q R₀ r₀) :
    Nonempty (Univ Q) := by
  obtain ⟨f₀, hf₀, -⟩ := (V.rep R₀).2 r₀ (hQP _ _ h₀)
  have hle : J ≤ RingHom.ker f₀ := (hJ R₀ f₀).1 (hf₀ ▸ h₀)
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top f₀ (top_le_iff.1 (h ▸ hle))
  haveI : Nontrivial (V.R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (V.R ⧸ J) :=
    co_quot O V.R (V.R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  refine ⟨⟨V.R ⧸ J, V.r.map (Ideal.Quotient.mkₐ O J), fun R' _ _ _ => ⟨fun f => ?_, fun r' hr' => ?_⟩⟩⟩
  · rw [glift_map_map, hJ]
    intro y hy
    show f (Ideal.Quotient.mk J y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
  · obtain ⟨f, hf, hu⟩ := (V.rep R').2 r' (hQP _ _ hr')
    have hk : J ≤ RingHom.ker f := (hJ R' f).1 (hf ▸ hr')
    have hc : (Ideal.Quotient.liftₐ J f hk).comp (Ideal.Quotient.mkₐ O J) = f := AlgHom.ext fun _ => rfl
    refine ⟨Ideal.Quotient.liftₐ J f hk, ?_, fun g hg => ?_⟩
    · show (V.r.map _).map _ = r'
      rw [glift_map_map, hc, hf]
    · have hg' : g.comp (Ideal.Quotient.mkₐ O J) = f := hu _ ((glift_map_map V.r _ g).symm.trans hg)
      exact Ideal.Quotient.algHom_ext O (hg'.trans hc.symm)

private theorem univ_norm {P : GCond O η Ψ} (V : Univ P) (c g₁ : Γ)
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : NormCond c g₁ P R₀ r₀) :
    Nonempty (Univ (NormCond c g₁ P)) := by
  refine univ_quot V (Ideal.span ({x | ∃ a b, x = ((V.r.hom c).mat - 1) a b} ∪
    {zmat c g₁ V.r.hom 0 1, zmat c g₁ V.r.hom 1 0})) (fun _ _ _ _ _ h => h.2) (fun R _ _ _ f => ?_) r₀ h₀
  have hz : ∀ a b, zmat c g₁ (V.r.map f).hom a b = f (zmat c g₁ V.r.hom a b) := fun a b => by
    simp only [zmat, Matrix.sub_apply, map_sub]
    rfl
  have hc : ∀ a b, (((V.r.map f).hom c).mat - 1) a b = f (((V.r.hom c).mat - 1) a b) := fun a b => by
    simp only [Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite f, map_one, map_zero]
    rfl
  rw [Ideal.span_le]
  constructor
  · rintro ⟨hn, -⟩ x hx
    show f x = 0
    rcases hx with ⟨a, b, rfl⟩ | rfl | rfl
    · rw [← hc, hn.atc, sub_self, Matrix.zero_apply]
    · rw [← hz, hn.z12]
    · rw [← hz, hn.z21]
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, (V.rep R).1 f⟩
    · rw [← sub_eq_zero]
      ext a b
      rw [hc]
      exact h (Or.inl ⟨a, b, rfl⟩)
    · rw [hz]
      exact h (Or.inr (Or.inl rfl))
    · rw [hz]
      exact h (Or.inr (Or.inr rfl))

private theorem univ_box {H : Type} [Group H] [TopologicalSpace H] {N : Set Γ} {ι : H →* Γ} (hι : Continuous ι)
    (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R)
    (V : Univ (Kills (O := O) (η := η) (Ψ := Ψ) N))
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : BoxCond N ι hι U I R₀ r₀) :
    Nonempty (Univ (BoxCond N ι hι U I)) := by
  obtain ⟨φ, hφ, -⟩ := (U.rep V.R).2 (V.r.comap ι hι) trivial
  refine univ_quot V (I.map φ) (fun _ _ _ _ _ h => h.1) (fun R _ _ _ f => ?_) r₀ h₀
  have hf : U.r.map (f.comp φ) = (V.r.map f).comap ι hι := by
    rw [← glift_map_map, hφ]
    exact GLift.ext rfl
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro ⟨-, f', hf', hI⟩
    obtain ⟨g, -, hu⟩ := (U.rep R).2 ((V.r.map f).comap ι hι) trivial
    have e : f' = f.comp φ := (hu f' hf').trans (hu _ hf).symm
    subst e
    exact fun y hy => hI hy
  · exact fun h => ⟨(V.rep R).1 f, f.comp φ, hf, fun y hy => h hy⟩

end Quot

end UpperTheory.V.U3

theorem UpperTheory.V.U3.exists_sRing :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
      {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} (hι : Continuous ι)
      (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) (cc g₁ : Γ), Marks η Ψ cc g₁ → LocGood U I →
      (∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) → (∀ g ∈ N, r0 η Ψ g = 1) →
      Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) →
      Nonempty (Univ (BoxCond N ι hι U I)) ∧ Nonempty (SRing N hι U I cc g₁) := by
  intro O _ _ _ _ _ Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ hM hL hΨ hN ⟨V⟩
  obtain ⟨x, τ, _, w, φ, hx, hφ, -⟩ := hL.chart
  have h₀ : BoxCond N ι hι U I O (baseLift O η Ψ hΨ) := by
    refine ⟨hN, x, GLift.ext hx, fun y hy => ?_⟩
    have h1 : φ y = 0 := by
      rw [← hφ.ker] at hy
      exact hy
    have h2 := hφ.const y
    rw [h1, map_zero] at h2
    exact IsFractionRing.injective O (FractionRing O) (h2.symm.trans (map_zero _).symm)
  obtain ⟨B⟩ := univ_box hι U I V _ h₀
  exact ⟨⟨B⟩, univ_norm B cc g₁ (baseLift O η Ψ hΨ) ⟨baseRepGL3_normalised_of_psi_eq_one η Ψ g₁ hM.Ψc, h₀⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelSigns
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem norm_mul_le_of_loc {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  by_cases h0 : f z = 0
  · simp [h0]
  have hp : 0 < ‖f z‖ := norm_pos_iff.2 h0
  have hx : ‖f x‖ ≤ 1 := by
    by_contra hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) (not_le.1 hx)
    have h1 := hf (x ^ n * z) (Ideal.mul_mem_left _ _ hz)
    rw [map_mul, map_pow, norm_mul, norm_pow] at h1
    have h2 := mul_lt_mul_of_pos_right hn hp
    rw [inv_mul_cancel₀ hp.ne'] at h2
    exact lt_asymm h1 h2
  exact mul_le_of_le_one_left hp.le hx

private theorem exists_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hsm : ∀ z ∈ s, z ∈ maximalIdeal R := fun z hz => hs ▸ Submodule.subset_span hz
  have hlt : (s.sup fun z => ‖f z‖₊) < 1 :=
    (Finset.sup_lt_iff (by norm_num)).2 fun z hz => hf z (hsm z hz)
  refine ⟨(s.sup fun z => ‖f z‖₊ : NNReal), NNReal.coe_nonneg _, hlt, fun z hz => ?_⟩
  have key : ∀ x : R, ‖f (x * z)‖ ≤ (s.sup fun z => ‖f z‖₊ : NNReal) := by
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro x
      exact (norm_mul_le_of_loc hf x (hsm z hz)).trans (Finset.le_sup (f := fun z => ‖f z‖₊) hz)
    | zero => intro x; simp
    | add a b _ _ ha hb =>
      intro x
      rw [mul_add, map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha x) (hb x))
    | smul a b _ hb =>
      intro x
      rw [smul_eq_mul, ← mul_assoc]
      exact hb _
  simpa using key 1

private theorem exists_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, h0, h1, h⟩ := exists_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (h b hb) (norm_nonneg _) (pow_nonneg h0 _)
      · rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
  exact ⟨n + 1, fun z hz => (key n z hz).trans_lt
    ((pow_le_pow_of_le_one h0 h1.le (Nat.le_succ n)).trans_lt hn)⟩

private theorem eq_of_dense {f f' : R →ₐ[O] K} (hf : IsLocPt f) (hf' : IsLocPt f') (s : K) (x : R)
    (T : Set R) (hT : ∀ y ∈ T, f' y = s * f y)
    (h : ∀ n : ℕ, ∃ y ∈ Submodule.span O T, x - y ∈ maximalIdeal R ^ n) : f' x = s * f x := by
  have hsp : ∀ y ∈ Submodule.span O T, f' y = s * f y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hT z hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, mul_add]
    | smul a b _ hb => rw [map_smul, map_smul, hb, mul_smul_comm]
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hs : 0 < ‖s‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow hf (div_pos hε hs)
  obtain ⟨n', hn'⟩ := exists_pow hf' (div_pos hε hs)
  obtain ⟨y, hy, hxy⟩ := h (max n n')
  have e : f' x - s * f x = f' (x - y) - s * f (x - y) := by
    rw [map_sub, map_sub, hsp y hy]; ring
  have a1 := hn _ (Ideal.pow_le_pow_right (le_max_left _ _) hxy)
  have a2 := hn' _ (Ideal.pow_le_pow_right (le_max_right _ _) hxy)
  rw [e, zero_add]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have a3 := mul_le_mul_of_nonneg_left a1.le (norm_nonneg s)
  have a4 : ε / (‖s‖ + 1) + ‖s‖ * (ε / (‖s‖ + 1)) = ε := by field_simp; ring
  linarith

end SlopeTestRemainingChoices

section Mon

variable {O R K Γ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field K] [Algebra O K] [Group Γ]

private theorem mon_zero (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] K) (e : ℤ)
    (h : ∀ g a b, e * wt a b < 0 → f ((r g).mat a b) = 0) (j : ℤ) (hj : e * j < 0) :
    ∀ y ∈ entMon r j, f y = 0 := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp at hj
  | cons s L ih =>
    rw [List.map_cons, List.sum_cons, mul_add] at hj
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hs : e * wt s.2.1 s.2.2 < 0
    · rw [h _ _ _ hs, zero_mul]
    · rw [ih (by omega), mul_zero]

private theorem mon_tor (r : Γ →* GG (m := 3) (R := R)) (f f' : R →ₐ[O] K) (t : Kˣ)
    (h : ∀ g a b, f' ((r g).mat a b) = ((t ^ wt a b : Kˣ) : K) * f ((r g).mat a b)) (j : ℤ) :
    ∀ y ∈ entMon r j, f' y = ((t ^ j : Kˣ) : K) * f y := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.prod_cons, map_mul, map_mul, h, ih, _root_.zpow_add,
      Units.val_mul]
    ring

private theorem mat_ker (η : Γ →* ℤˣ) (r : Γ →* GG (m := 3) (R := R)) (c : Γ) (hc : η c = -1) (h1 : (r c).mat = 1) (g : Γ) :
    ∃ g' ∈ η.ker, (r g).mat = (r g').mat := by
  rcases Int.units_eq_one_or (η g) with h | h
  · exact ⟨g, h, rfl⟩
  · refine ⟨g * c⁻¹, by simp [MonoidHom.mem_ker, h, hc], ?_⟩
    have hl : (r c).left = 1 := Units.ext h1
    have e : g = g * c⁻¹ * c := by simp
    conv_lhs => rw [e]
    rw [map_mul r _ c, GG.mat, GG.mat, SemidirectProduct.mul_left, hl, map_one, mul_one]

end Mon

theorem UpperTheory.V.U3.model_signs :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f →
        (NegZero M.𝒜 (f.comp M.q) ↔ Upper η (push f S.r.hom)) ∧ (PosZero M.𝒜 (f.comp M.q) ↔ Lower η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → ∀ t : (PadicAlgCl l)ˣ,
          push f' S.r.hom = conjBy (tor _ t) (push f S.r.hom) → f'.comp M.q = act M.𝒜 (tz t) (f.comp M.q) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M _ hM f hf
  have h1 : (S.r.hom cc).mat = 1 := ((S.rep S.R).1 (AlgHom.id _ _)).1.atc
  have key : ∀ e : ℤ, (∀ j, e * j < 0 → ∀ x ∈ M.𝒜 j, f (M.q x) = 0) ↔
      ∀ g ∈ η.ker, ∀ a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
    intro e
    constructor
    · intro h g _ a b hab
      obtain ⟨x, hx, hq⟩ := M.ent g a b
      rw [← hq]
      exact h _ hab x hx
    · intro h j hj x hx
      have h' : ∀ g a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
        intro g a b hab
        obtain ⟨g', hg', e'⟩ := mat_ker η S.r.hom cc hM.ηc h1 g
        rw [e']
        exact h g' hg' a b hab
      have := eq_of_dense hf hf 0 (M.q x) (entMon S.r.hom j)
        (fun y hy => by rw [mon_zero _ f e h' j hj y hy, zero_mul]) (M.dense j x hx)
      rwa [zero_mul] at this
  refine ⟨?_, ?_, fun f' hf' t ht => ?_⟩
  · have := key 1
    simp only [one_mul] at this
    exact this
  · have := key (-1)
    simp only [neg_mul, one_mul, neg_lt_zero] at this
    exact this
  · have h' : ∀ g a b, f' ((S.r.hom g).mat a b) =
        ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * f ((S.r.hom g).mat a b) := by
      intro g a b
      have := (conjBy_tor (push f S.r.hom) t).1 g a b
      rw [← ht] at this
      exact this
    refine AlgHom.ext fun x => ?_
    induction x using DirectSum.Decomposition.inductionOn M.𝒜 with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | @homogeneous j x =>
      rw [act_of_mem M.𝒜 _ _ x.2]
      exact eq_of_dense hf hf' _ (M.q x) (entMon S.r.hom j) (mon_tor _ f f' t h' j) (M.dense j x x.2)
end

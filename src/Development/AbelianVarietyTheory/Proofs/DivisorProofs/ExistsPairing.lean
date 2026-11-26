module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvOfFamAffine
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.TwistDescent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem memKL_of_lam_eq_zero {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (hx : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0) : GlobalTheory.MemKL A L x := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

end GlobalTheory.DualCon.TwistDescent

namespace GlobalTheory.DualCon

end GlobalTheory.DualCon
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelPointPairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hA : IsAbelianScheme A) {L : LB (G2 A).left} (hL : L.IsLB) {T : Over S} (a b c : T ⟶ G2 A) :
    pull (a * b * c).left (cls L hL) - pull (a * b).left (cls L hL) - pull (a * c).left (cls L hL)
      - pull (b * c).left (cls L hL) + pull a.left (cls L hL) + pull b.left (cls L hL) + pull c.left (cls L hL)
      - pull (1 : T ⟶ G2 A).left (cls L hL) = 0 := by
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨t, ht⟩ := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hA2 L hL T a b c
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_eight] at e
  simp at e
  rw [← e]
  abel


omit [IsCommMonObj A] in
theorem pull_eq_zero_of_factor {X : Scheme.{0}} {c : Pic X} {Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : pull f c = 0) : pull (g ≫ f) c = 0 := by
  rw [pull_comp, h, map_zero]

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem lam_eq_zero (hA : IsAbelianScheme A)
    (h₁ : pull (lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0)
    (h₂ : pull (lift (𝟙 A) (1 : A ⟶ A)).left (cls P hP) = 0) {T : Over S} (x : T ⟶ A)
    (hx : pull (lift (snd A T ≫ x) (fst A T)).left (cls P hP) = 0) :
    lam (cls P hP) (fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A)) (snd T (G2 A)) = 0 := by
  let W := T ⊗ G2 A
  let x' : W ⟶ A := fst T (G2 A) ≫ x
  let b₁ : W ⟶ A := snd T (G2 A) ≫ fst A A
  let b₂ : W ⟶ A := snd T (G2 A) ≫ snd A A
  have l₁ : ∀ b : W ⟶ A, DiagPairing.pc hP 1 b = 0 := fun b => by
    have e : (lift (1 : W ⟶ A) b) = b ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₁
  have l₂ : ∀ a : W ⟶ A, DiagPairing.pc hP a 1 = 0 := fun a => by
    have e : (lift a (1 : W ⟶ A)) = a ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₂
  have l₃ : DiagPairing.pc hP x' b₂ = 0 := by
    have e : (lift x' b₂) = lift b₂ (fst T (G2 A)) ≫ lift (snd A T ≫ x) (fst A T) := by
      rw [comp_lift, lift_snd_assoc, lift_fst]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ hx
  have one : (1 : W ⟶ G2 A) = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ea : fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A) = lift x' 1 := by
    rw [comp_lift, MonObj.comp_one]
  have eb : snd T (G2 A) = lift b₁ b₂ := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have e := cube_cls hA hP (lift x' 1) (lift b₁ 1) (lift 1 b₂)
  simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, one] at e
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP (x' * b₁) 1 - DiagPairing.pc hP x' b₂
    - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP x' 1 + DiagPairing.pc hP b₁ 1 + DiagPairing.pc hP 1 b₂
    - DiagPairing.pc hP 1 1 = 0 at e
  rw [l₁, l₁, l₂, l₂, l₂, l₃] at e
  rw [lam, ea, eb, one, lift_mul_lift, _root_.one_mul]
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP x' 1 - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP 1 1 = 0
  rw [l₁, l₂, ← e]
  abel

end GlobalTheory.KernelPointPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfPowEqOneOfGeometric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeRel
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_pow_eq_one_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A →
    ∀ (m : ℕ), 0 < m → IsUnit ((m : Γ(S, ⊤))) → ∀ (T : Over S) (x : T ⟶ A), x ^ m = 1 →
      (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (q : Spec (CommRingCat.of κ) ⟶ T.left),
        (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = 1) → x = 1 := by
  intro S A _ _ hA m _ hm T x hx hgeo
  let f := (ReciprocityTheory.ChartRestriction.G.Out.mulA A m).left
  haveI : FormallyUnramified f := GlobalTheory.formallyUnramified_mulA S A m hm
  haveI : Smooth A.hom := hA.smooth
  have hfA : f ≫ A.hom = A.hom := Over.w _
  haveI : LocallyOfFiniteType (f ≫ A.hom) := by rw [hfA]; infer_instance
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have hpow : ∀ y : T ⟶ A, y ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA A m = y ^ m := fun y => by
    simp [ReciprocityTheory.ChartRestriction.G.Out.mulA, MonObj.comp_pow]
  have hf : x.left ≫ f = (1 : T ⟶ A).left ≫ f := by
    have e1 := congrArg CommaMorphism.left (hpow x)
    have e2 := congrArg CommaMorphism.left (hpow 1)
    simp only [Over.comp_left] at e1 e2
    rw [e1, e2, hx, one_pow]
  let p : T.left ⟶ pullback f f := pullback.lift x.left (1 : T ⟶ A).left hf
  have hr : Set.range p ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨t, rfl⟩
    let κ : Type := AlgebraicClosure (T.left.residueField t)
    let q : Spec (CommRingCat.of κ) ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) κ)) ≫ T.left.fromSpecResidueField t
    have hq : (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ 1 := by
      rw [hgeo κ q, MonObj.comp_one]
    have hq' : q ≫ x.left = q ≫ (1 : T ⟶ A).left := by
      have h0 := congrArg (fun h => h.left) hq
      simp only [Over.comp_left, Over.homMk_left] at h0
      exact h0
    have e : q ≫ p = (q ≫ x.left) ≫ pullback.diagonal f := by
      refine pullback.hom_ext ?_ ?_
      · simp only [p, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [p, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hq']
    refine ⟨(q ≫ x.left) (IsLocalRing.closedPoint κ), ?_⟩
    have hqt : q (IsLocalRing.closedPoint κ) = t :=
      Scheme.fromSpecResidueField_apply t _
    have e2 : p (q (IsLocalRing.closedPoint κ)) =
        pullback.diagonal f ((q ≫ x.left) (IsLocalRing.closedPoint κ)) :=
      congrArg (fun h => h (IsLocalRing.closedPoint κ)) e
    rw [hqt] at e2
    exact e2.symm
  let g := IsOpenImmersion.lift (pullback.diagonal f) p hr
  have hg := IsOpenImmersion.lift_fac (pullback.diagonal f) p hr
  have h1 : x.left = g := by
    have h0 := congrArg (· ≫ pullback.fst f f) hg
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, p, pullback.lift_fst] at h0
    exact h0.symm
  have h2 : (1 : T ⟶ A).left = g := by
    have h0 := congrArg (· ≫ pullback.snd f f) hg
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, p, pullback.lift_snd] at h0
    exact h0.symm
  exact Over.OverMorphism.ext (h1.trans h2.symm)

end GlobalTheory.TorsionRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToP
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.KerPowDescent

theorem pow_eq_one_of_lift {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S} [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A')
    [IsMonHom ψ] (m : ℕ) {P' : LB (G2 A').left} (hP' : P'.IsLB)
    (hiso : LBIso (Hecke.lbPow o.P m) (P'.pull (sq2 ψ))) {e₀ : ℕ}
    (hker : ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e₀ = 1)
    {T T' : Over S} (π' : T' ⟶ T) (y : T' ⟶ o.A) (x : T ⟶ A') (hy : y ≫ ψ = π' ≫ x)
    (h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0) : y ^ (m * e₀) = 1 := by
  have hP := o.isLB
  have hPm : (Hecke.lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left
        (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, Hecke.evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rwa [← pow_mul] at h4

theorem kernel_primePower_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b N S s o c hc hpu H A' _ _ ψ hA' hψ hG hH P' hP' r₁ r₂ hiso
  haveI := hψ
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  obtain ⟨e, rfl⟩ := hc
  refine ⟨e₀, he₀, ?_⟩
  intro T x hx
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  have hxc : x ^ (p ^ e * e₀) = 1 := by
    let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
    let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
    let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
      show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
      rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
    have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
      show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
      exact pullback.condition.symm)
    have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker π' y x hy h0
    have h5 : π' ≫ x ^ (p ^ e * e₀) = π' ≫ 1 := by
      rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h6 := congrArg (fun f => f.left) h5
    simp only [Over.comp_left] at h6
    exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6
  have hu : IsUnit (((p ^ e : ℕ) : Γ(S, ⊤))) := by
    have := (hpu.pow e).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  refine GlobalTheory.TorsionRigid.eq_one_of_pow_eq_one_of_geometric S A' hA' (p ^ e)
    (pow_pos (Fact.out : p.Prime).pos e) hu T (x ^ e₀) (by rw [← pow_mul, mul_comm]; exact hxc) ?_
  intro κ _ _ q
  let Tq : Over S := Over.mk (q ≫ T.hom)
  let πq : Tq ⟶ T := Over.homMk q rfl
  obtain ⟨pt, hpt⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left (q ≫ x.left)
  let y : Tq ⟶ o.A := Over.homMk pt (by
    show pt ≫ o.A.hom = q ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← hpt, Category.assoc, Over.w x])
  have hy : y ≫ ψ = πq ≫ x := Over.OverMorphism.ext (by
    show pt ≫ ψ.left = q ≫ x.left
    exact hpt.symm)
  have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker πq y x hy h0
  have hg : (y ^ e₀) ^ (p ^ e) = 1 := by rw [← pow_mul, mul_comm]; exact h4
  have hgψ : (y ^ e₀) ≫ ψ = (πq ≫ x) ^ e₀ := by rw [GlobalTheory.SS.FrobTorsion.pow_comp', hy]

  have hz : GlobalTheory.AbDual.evc hP' (snd A' Tq ≫ (y ^ e₀) ≫ ψ) (fst A' Tq) = 0 := by
    have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst A' Tq) (snd A' Tq ≫ πq)).left) h0
    rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst] at h1
    simp only [Category.assoc] at h1
    rw [hgψ, comp_pow, Hecke.evc_pow_left hA' hP' r₁ r₂, h1, smul_zero]
  have hG0 := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 A') := AbelianSchemeGerms.isAbelianScheme_tensor A' A' hA' hA'
  have hAo2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have s₁ : GlobalTheory.CechPic.pull (lift (1 : A' ⟶ A') (𝟙 A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₁
  have s₂ : GlobalTheory.CechPic.pull (lift (𝟙 A') (1 : A' ⟶ A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₂
  have hK : GlobalTheory.MemKL (G2 A') P' (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') :=
    GlobalTheory.DualCon.TwistDescent.memKL_of_lam_eq_zero hP' _
      (GlobalTheory.KernelPointPairing.lam_eq_zero hP' hA' s₁ s₂ ((y ^ e₀) ≫ ψ) hz)
  have w₀ : Out.WeilIs (G2 A') P' 1 (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') 1 1 :=
    GlobalTheory.DescendedPrincipal.weilIs_one_right hG0 hA2 hP' fun pp => by
      obtain ⟨V, hV, c, hc⟩ := hK pp
      exact ⟨V, hV, GlobalTheory.DescendedPrincipal.exists_theta_of_translDiff hP' _ V c hc⟩
  have hPc : (Hecke.lbPow o.P (p ^ e)).IsLB := LB.isLB_linComb o.isLB _ _
  let ψ2 : G2 o.A ⟶ G2 A' := lift (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
  haveI : IsMonHom ψ2 := inferInstance
  have hw : LBIso (Geo.Tor.lbPow (Hecke.lbPow o.P (p ^ e)) 1) (P'.pull ψ2.left) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hPc 1) hPc (pull_isLB hP' _) (GlobalTheory.lbIso_lbPow_one hPc) hiso
  have hHψ : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hG.inv ⟨h, hh⟩)
  obtain ⟨h, hh, hgh⟩ := hH κ (q ≫ T.hom) (y ^ e₀) hg fun h hh => by
    have e1 : (lift (y ^ e₀) 1 : Tq ⟶ G2 o.A) ≫ ψ2 = lift ((y ^ e₀) ≫ ψ) 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    have e2 : (lift 1 (toUnit Tq ≫ h) : Tq ⟶ G2 o.A) ≫ ψ2 = 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, Category.assoc, hHψ h hh, MonObj.comp_one]
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG0 hAo2 hPc hP' ψ2 hw (n := 1) (x := lift (y ^ e₀) 1)
      (y := lift 1 (toUnit Tq ≫ h)) (c := 1) (by rw [e1, e2]; exact w₀)
    simpa using this
  show πq ≫ x ^ e₀ = 1
  rw [comp_pow, ← hgψ, hgh, Category.assoc, hHψ h hh, MonObj.comp_one]

end GlobalTheory.UPel.HT.ES.KerPowDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToPStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_primeToP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (exact GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (intros; apply GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeQuotientByPGroupSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeQuotientByPGroupSections
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.Hecke.TateQuot

theorem exists_pow_inv (c n : ℕ) (h : c.Coprime n) :
    ∃ u : ℕ, ∀ {G : Type} [Monoid G] (q : G), q ^ n = 1 → q ^ (c * u) = q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    exact ⟨1, fun q _ => by rw [h, _root_.one_mul, pow_one]⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨(((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val, fun q hq => ?_⟩
  have e : (c * (((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val) % n = 1 % n := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← ZMod.val_one_eq_one_mod]
    congr 1
    have := (ZMod.unitOfCoprime c h).mul_inv
    rwa [ZMod.coe_unitOfCoprime] at this
  rw [pow_eq_pow_mod _ hq, e, ← pow_eq_pow_mod _ hq, pow_one]

theorem comp_pow_pt {S : Scheme.{0}} {A : Over S} [GrpObj A] {T U : Over S} (f : T ⟶ U) (g : U ⟶ A) (m : ℕ) :
    f ≫ g ^ m = (f ≫ g) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_tateIsoO_quot : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ h ∈ H, h ^ c = 1) → ∀ (act' : OActN D.O A'), (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  intro p _ D R _ b N S s o c hc H A' _ _ ψ hA' hψ hGal hHc act' hact P' hP' r₁ r₂ hiso κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  obtain ⟨e₀, rfl⟩ := hc
  have hcop : ∀ n : ℕ, n.Coprime p → (p ^ e₀).Coprime n := fun n hnp => Nat.Coprime.pow_left e₀ hnp.symm
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have hkill : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 → t ^ (p ^ e₀) = 1 := by
    intro t ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt, ← comp_pow_pt, hHc h.1 h.2, MonObj.comp_one]
  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev n y ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    constructor
    · intro h1
      have h2 := hkill _ h1
      have h3 : I.ev n y ^ n = 1 := by
        rw [← TateTransl.ev_nsmul]; exact (I.ker n hn hnp _).2 ⟨y, rfl⟩
      have h4 : I.ev n y ^ (p ^ e₀).gcd n = 1 := pow_gcd_eq_one.2 ⟨h2, h3⟩
      rw [hcop n hnp, pow_one] at h4
      exact (I.ker n hn hnp y).1 h4
    · rintro ⟨z, rfl⟩
      rw [(I.ker n hn hnp _).2 ⟨z, rfl⟩, MonObj.one_comp]
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev n y ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev n y ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      have hanc := hkill _ han
      obtain ⟨u, hu⟩ := exists_pow_inv (p ^ e₀) n (hcop n hnp)
      have ha' : (a ^ (p ^ e₀ * u)) ^ n = 1 := by
        rw [← pow_mul, show p ^ e₀ * u * n = n * p ^ e₀ * u by ring, pow_mul, pow_mul, hanc, one_pow]
      obtain ⟨y, hy⟩ := (I.onto n hn hnp _).1 ha'
      refine ⟨y, ?_⟩
      rw [hy, ← hΨ, map_pow, hΨ, ha, hu q hq]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e₀))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]
  refine ⟨⟨fun n => I.ζ n ^ (p ^ e₀), fun n hn hnp => (I.ζ_prim n hn hnp).pow_of_coprime _ (hcop n hnp), ?_,
    fun n y => I.ev n y ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · intro n m hn hm hnm
    rw [← pow_mul, _root_.mul_comm (p ^ e₀) m, pow_mul, I.ζ_pow n m hn hm hnm]
  · intro n y y'
    rw [I.add, MonObj.mul_comp]
  · intro n b' y
    rw [I.lin, Category.assoc, hact, ← Category.assoc]
  · exact fun n hn hnp y => ker' n hn hnp y
  · exact fun n hn hnp q => onto' n hn hnp q
  · intro n m hn hm hnm y
    rw [← hΨ, ← map_pow, hΨ, I.tower n m hn hm hnm]
  · intro n hn hnp u v
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn
      (hnκ n hnp) _ _ (htor n hn hnp u) (htor n hn hnp v)
    have h3 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S o.A A' ψ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      (P'.pull (lift (𝟙 A') (𝟙 A')).left) (p ^ e₀) n (Over.mk x) (I.ev n u) (I.ev n v)
      (unitOn (I.ζ n ^ (2 * D.EF u v))) e o.ab hA' (pull_isLB o.isLB _) (pull_isLB hP' _) hψ hiso2 he).2
      (I.isom n hn hnp u v)
    rw [h3] at he
    convert he using 2
    show unitOn ((I.ζ n ^ (p ^ e₀)) ^ (2 * D.EF u v)) = unitOn (I.ζ n ^ (2 * D.EF u v)) ^ (p ^ e₀)
    rw [unitOn, unitOn, ← map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · show toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y ≫ ψ
    rw [← Category.assoc, hI]

end GlobalTheory.UPel.HT.Hecke.TateQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeQuotientByPGroupSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateSimilitude_quotient_by_pGroup_sections : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ h ∈ H, h ^ c = 1) → ∀ (act' : OActN D.O A'), (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.TateQuot.exists_tateIsoO_quot) | (exact GlobalTheory.UPel.HT.Hecke.TateQuot.exists_tateIsoO_quot) | (intros; apply GlobalTheory.UPel.HT.Hecke.TateQuot.exists_tateIsoO_quot  <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.PQuot

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem sections_triv {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ^ c = 1) :
    (∃ t : ((Hecke.lbPow o.P c).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧
    (∃ t : ((Hecke.lbPow o.P c).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  have hP := o.isLB
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb hP _ _
  have clsPow : GlobalTheory.CechPic.cls (Hecke.lbPow o.P c) hQ = c • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin c) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = c • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow, map_nsmul]
  have hQth : GlobalTheory.AbDual.evc hQ (toUnit o.A ≫ h) (𝟙 o.A) = 0 := by
    rw [evcQ, ← evc_pow_left o.ab hP o.rig₁ o.rig₂, ← MonObj.comp_pow, hh, MonObj.comp_one]
    exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

theorem exists_quot {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : ∃ e : ℕ, c = p ^ e) (hp : IsUnit ((p : ℕ) : R))
    (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (hfin : Finite H)
    (hfree : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ H →
      toUnit (Over.mk x) ≫ h = 1 → h = 1)
    (stab : ∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) (hpow : ∀ h ∈ H, h ^ c = 1)
    (hiso : ∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1)
    (hmax : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 →
      (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A)
        (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) :
    ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧
      ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A),
        g ≫ ψ = 1 ↔ ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h := by
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.T.exists_abelianScheme_quotient_by_finite_translations S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    H o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  choose actf hactf using fun c' : D.O => GlobalTheory.T.exists_descent_endomorphism_quotient_group_scheme S o.A A' H ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ c H
    (fun h hh => (sections_triv o c h (hpow h hh)).1) (fun h hh => (sections_triv o c h (hpow h hh)).2) hiso
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' H ψ hψ hgal
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (sq2 ψ) _ _
    (Hecke.lbPow o.P c) hGC (DVR.linComb_isLB _ o.isLB _ _) u hu hcoc
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b N S s o A' ψ hψ _ P₀ hP₀ w₀
  have hc1 : 1 ≤ c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient p D R b N S s o A' act' ψ _ _ hA' hψ hgal hcomp
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b N S s o A' ψ _ hA' hψ hgal _ P' hP' w r1 r2
      ample := GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b N S s o A' ψ _ hA' hψ hgal _ hc1 P' hP' w
      kerP := GlobalTheory.T.descendedBundle_kernel_killed_primeToP p D R b N S s o c hc hp H A' ψ hA' hψ hgal hmax P' hP' r1 r2 w
      rosati := GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b N S s o A' act' ψ _ hA' hψ hgal hcomp _ P' hP' w r1 r2
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta x ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (c' • x) ≫ ψ = (o.eta x ≫ ψ) ≫ act'.act c'
        rw [o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, one_comp]
      geom := GlobalTheory.T.exists_tateSimilitude_quotient_by_pGroup_sections p D R b N S s o c hc H A' ψ hA' hψ hgal hpow act' hcomp P' hP' r1 r2 w }
  have hmk : IsMonHom (𝟙 o.A ^ c) := GlobalTheory.AbLaw.MulN.isMonHom_mulA o.A c
  obtain ⟨ψ', hψ'h, hψ'⟩ := GlobalTheory.T.exists_descent_hom_quotient_galois_group_scheme S o.A A' o.A H ψ hψ hgal (𝟙 o.A ^ c) hmk
    (fun h hh => by rw [MonObj.comp_pow, Category.comp_id, hpow h hh])
  refine ⟨o', ψ, ⟨hc, hψ, hcomp, fun x => rfl, ⟨w⟩, ψ', hψ'h, hψ', ?_⟩, fun κ _ _ x t => ⟨fun ht => ?_, ?_⟩⟩
  · show ψ' ≫ ψ = 𝟙 A' ^ c
    rw [← cancel_epi ψ, ← Category.assoc, hψ', MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have ht' : t ≫ ψ = (1 : Over.mk x ⟶ A') := ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht', MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hgal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    refine ⟨h.1, h.2, ?_⟩
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt]
  · rintro ⟨h, hh, rfl⟩
    show (toUnit (Over.mk x) ≫ h) ≫ ψ = (1 : Over.mk x ⟶ A')
    rw [Category.assoc, kill h hh, MonObj.comp_one]

theorem exists_pairing {s : S ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : ∃ e : ℕ, c = p ^ e)
    (κ : Type) [Field κ] [IsAlgClosed κ] (hp : ((p : ℕ) : κ) ≠ 0) (x : Sp κ ⟶ S) :
    ∃ e : (Over.mk x ⟶ o.A) → (Over.mk x ⟶ o.A) → κˣ,
      (∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : Over.mk x ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : Over.mk x ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : Over.mk x ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ c = 1 → (∀ g' : Over.mk x ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) := by
  have hcκ : (c : κ) ≠ 0 := by
    obtain ⟨e, rfl⟩ := hc
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hp
  obtain ⟨e, he, hl, hr⟩ := GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes S o.A o.P o.ab o.isLB κ x c hcκ
  have hG2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hinj : Function.Injective (unitOn (R := κ)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of κ)).symm.commRingCatIsoToRingEquiv.injective
  have hmul : ∀ u v : κˣ, unitOn (u * v) = unitOn u * unitOn v := fun u v => map_mul (Units.map _) u v
  have hone : unitOn (1 : κˣ) = 1 := map_one (Units.map _)
  have hval : ∀ g g' : Over.mk x ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      Out.WeilIs (G2 o.A) o.P c (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 g') (unitOn (e g g')) :=
    fun g g' hg hg' => GlobalTheory.BiextPairing.weilIs_of_hecke_lbPow hG2 o.isLB c ((he g g' hg hg' _).2 rfl)
  have hact : ∀ (a : D.O) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (g ≫ o.act.act a) ^ c = 1 := fun a g hg => by
    haveI := o.act.hom a
    rw [← MonObj.pow_comp, hg, MonObj.one_comp]
  refine ⟨e, he, hl, hr, fun a g g' hg hg' => hinj ?_, fun g g' hg hg' => hinj ?_, fun g hg h => ?_⟩
  · exact GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso S o.A o.P o.ab o.isLB _ _ (o.act.hom a) (o.act.hom _) (o.rosati a) c _ g g' _ _
      (hval _ _ (hact a g hg) hg') (hval _ _ hg (hact _ g' hg'))
  · have h1 := GlobalTheory.CommPairing.weilIs_symm o.isLB (hval g' g hg' hg)
    have h2 := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm c _ g g' _ _ h1 (hval g g' hg hg')
    rw [hmul, hone, ← h2]
    exact inv_mul_cancel _
  · obtain ⟨e₀, he₀, hker⟩ := o.kerP
    have h1 := hker _ g (GlobalTheory.T.lineBundle_slice_trivial_of_weilPairing_one_torsion S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ κ x c hcκ g hg (fun g' hg' => by
      have := hval g g' hg hg'
      rwa [h g' hg', hone] at this))
    have hco : e₀.Coprime c := by
      obtain ⟨e, rfl⟩ := hc
      exact he₀.pow_right e
    exact (pow_eq_one_iff_of_coprime hco).1 ⟨h1, hg⟩

theorem max_geom {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp R} (o : Obj b N s) (c : ℕ) (hc : (c : k) ≠ 0)
    (H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A)) (hpow : ∀ h ∈ H, h ^ c = 1)
    (hmax : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H)
    (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ o.A) (hg : g ^ c = 1)
    (ho : ∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A)
        (lift 1 (toUnit (Over.mk x) ≫ h)) 1) : ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h := by
  obtain ⟨g₀, hg₀, rfl⟩ := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hc).2 κ x g hg
  refine ⟨g₀, hmax g₀ hg₀ fun h hh => ?_, rfl⟩
  obtain ⟨e, he, -, -⟩ := GlobalTheory.T.exists_bimultiplicative_weilPairing_torsion_axes (Sp k) o.A o.P o.ab o.isLB k (𝟙 _) c hc
  have hG2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  obtain ⟨u, hu⟩ : ∃ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
      (lift g₀ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) u := ⟨_, (he g₀ h hg₀ (hpow h hh) _).2 rfl⟩
  have h1 := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hG2 hQ (toUnit (Over.mk x)) hu
  rw [comp_lift, comp_lift, MonObj.comp_one] at h1
  have h2 := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hG2 hQ h1 (ho h hh)
  have hinj : Function.Injective (toUnit (Over.mk x)).left.appTop.hom := by
    have e1 : (toUnit (Over.mk x)).left = x := by simp
    rw [e1]
    haveI : Nontrivial Γ(Sp κ, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    letI : Field Γ(Sp k, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)).toField
    exact RingHom.injective x.appTop.hom
  have hu1 : u = 1 := Units.map_injective (f := (toUnit (Over.mk x)).left.appTop.hom.toMonoidHom) hinj
    (h2.trans (map_one _).symm)
  rwa [hu1] at hu

end GlobalTheory.UPel.HT.ES.PQuot

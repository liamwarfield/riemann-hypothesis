module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
open CategoryTheory UpperTheory.Gal.Int.Geo

theorem UpperTheory.quotient_unique_of_comp :
    QComp → QUniq := by
  intro hQ q _ D R R' _ _ _ b gb N N₀ c h3 hc X X₁ s s₁ o u f n n'
  obtain ⟨u', ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback q D R b N₀ X₁ X s₁ (f ≫ s₁) f rfl u

  have down : ∀ k : QMap o u f c, ∃ k₁ : QMap o u' (𝟙 X) c, k.φ = k₁.φ ≫ m.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u (𝟙 X ≫ f) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨k₁, h₁⟩ := (hQ q D R R' b gb N N₀ c X X X₁ s (f ≫ s₁) s₁ o u' u (𝟙 X) f).2.1 k₀ m
    exact ⟨k₁, hk ▸ h₁⟩
  obtain ⟨n₁, h₁⟩ := down n
  obtain ⟨n₂, h₂⟩ := down n'

  have self : ∀ k : QMap o u' (𝟙 X) c, ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k.φ = n₁.φ ≫ a.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u' (𝟙 X ≫ 𝟙 X) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k₀.φ = n₁.φ ≫ a.φ :=
      (hQ q D R R' b gb N N₀ c X X X s (f ≫ s₁) (f ≫ s₁) o u' u' (𝟙 X) (𝟙 X)).2.2.1
        inferInstance n₁ k₀
    exact ⟨a₀, hk ▸ ha₀⟩
  obtain ⟨a, ha⟩ := self n₁
  obtain ⟨a', ha'⟩ := self n₂
  have hr : a.φ = a'.φ := GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique q D R b N₀ h3 hc X X (f ≫ s₁) (f ≫ s₁) u' u' (𝟙 X) a a'
  rw [h₁, h₂, ha', ← hr, ← ha]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem UpperTheory.isogeny_class_exists_of_quotient :
    QObj → QComp → QUniq → QLev → ClsEx := by
  intro hObj hComp hUniq hLev q _ D R R' _ _ _ b gb β hM N N₀ c a 𝔞 hN hpos h3 hcop hgen Y X s o
  obtain ⟨o₀, ⟨n⟩⟩ := hObj q D R R' b gb β hM N N₀ c hN hpos hcop X s o
  obtain ⟨l, hl, hln⟩ := hLev q D R R' b gb N N₀ c a 𝔞 hpos hgen X s _ o o₀ n
  obtain ⟨f, ⟨hfs, m, hm⟩, hfu⟩ := Y.rep X _ o₀ l hl
  have key : ∀ (j : X ⟶ Y.X), j ≫ Y.s = s ≫ spMap β → ∀ (k : QMap o Y.univ j c),
      (∀ y : D.La, Over.Hom.left (o.eta ((algebraMap (NumberField.RingOfIntegers D.F) D.O) a • y)) ≫ k.φ =
        j ≫ Over.Hom.left (Y.lv y)) → j = f := by
    intro j hj k hk
    obtain ⟨k', hk'⟩ : ∃ k' : QMap o Y.univ (𝟙 X ≫ j) c, k'.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨m', hm'⟩ :=
      (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) j).2.2.1 inferInstance n k'
    apply hfu
    refine ⟨hj, m', fun y => ?_⟩
    rw [← hln y, Category.assoc, ← hm', hk']
    exact hk y
  obtain ⟨n', hn'⟩ := (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) f).1 n m
  refine ⟨⟨⟨𝟙 X ≫ f, by rw [Category.id_comp, hfs], n', fun y => ?_⟩⟩, ?_⟩
  · rw [hn', ← Category.assoc, hln y, hm y, Category.id_comp]
  · intro C C'
    obtain ⟨j, ov, k, hk⟩ := C
    obtain ⟨j', ov', k', hk'⟩ := C'
    have e1 := key j ov k hk
    have e2 := key j' ov' k' hk'
    subst e1
    subst e2
    exact ⟨rfl, hUniq q D R R' b gb N N₀ c h3 hcop X Y.X s Y.s o Y.univ _ k k'⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo.QCompPf

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {b : Base D R} {gb : GBase D.toG R'} {N N₀ c : ℕ} {X X' X₁ X₂ : Scheme.{0}} {s : X ⟶ Sp R'}
  {s' : X' ⟶ Sp R'} {s₁ : X₁ ⟶ Sp R} {s₂ : X₂ ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'}
  {u₁ : Obj b N₀ s₁} {u₂ : Obj b N₀ s₂} {f : X ⟶ X₁} {g : X₁ ⟶ X₂} {e : X' ⟶ X}

private def after (n : QMap o u₁ f c) (m : ObjMap u₁ u₂ g) : QMap o u₂ (f ≫ g) c where
  φ := n.φ ≫ m.φ
  φ₂ := n.φ₂ ≫ m.φ₂
  cart := n.cart.comp m.cart
  sq := MapComp.isSquare_comp n.sq m.sq
  act x := by
    have h₁ := n.act x
    have h₂ := m.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (n.pol).trans o.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
    (MapComp.lbIso_pull_comp m.pol n.φ₂ rfl)
  eta y := by
    have h₁ := n.eta y
    have h₂ := m.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private def before (m : GObjMap o' o e) (n : QMap o u₁ f c) : QMap o' u₁ (e ≫ f) c where
  φ := m.φ ≫ n.φ
  φ₂ := m.φ₂ ≫ n.φ₂
  cart := m.cart.comp n.cart
  sq := MapComp.isSquare_comp m.sq n.sq
  act x := by
    have h₁ := m.act x
    have h₂ := n.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (m.pol).trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u₁.isLB _)
    (MapComp.lbIso_pull_comp n.pol m.φ₂ rfl)
  eta y := by
    have h₁ := m.eta (c • y)
    have h₂ := n.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private theorem factor (n' : QMap o u₂ (f ≫ g) c) (m : ObjMap u₁ u₂ g) :
    ∃ n : QMap o u₁ f c, n'.φ = n.φ ≫ m.φ := by
  have hw : n'.φ ≫ u₂.A.hom = (o.A.hom ≫ f) ≫ g := by
    rw [n'.cart.1.w, Category.assoc]
  let ℓ : o.A.left ⟶ u₁.A.left := m.cart.1.lift n'.φ (o.A.hom ≫ f) hw
  have hℓφ : ℓ ≫ m.φ = n'.φ := m.cart.1.lift_fst _ _ _
  have hℓs : ℓ ≫ u₁.A.hom = o.A.hom ≫ f := m.cart.1.lift_snd _ _ _
  obtain ⟨ℓ₂, hsq⟩ := MapComp.exists_isSquare (G := u₁.A) (G' := o.A) hℓs
  have hsq₂ : ℓ₂ ≫ m.φ₂ = n'.φ₂ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hsq m.sq)
    rw [hℓφ]
    exact n'.sq
  refine ⟨⟨ℓ, ℓ₂, ?_, hsq, ?_, ?_, ?_⟩, hℓφ.symm⟩
  · exact IsGrpPullback.cancel m.cart (IsGrpPullback.congr n'.cart rfl hℓφ.symm) hℓs
  · intro x
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, m.act x, ← Category.assoc, hℓφ]
      exact n'.act x
    · rw [Category.assoc, Category.assoc, hℓs, Over.w, hℓs, ← Category.assoc, Over.w]
  · exact LBIso.trans o.isLB (pull_isLB u₂.isLB _) (pull_isLB u₁.isLB _) n'.pol
      (MapComp.lbIso_pull_comp m.pol ℓ₂ hsq₂.symm).symm
  · intro y
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, n'.eta y, m.eta y, Category.assoc]
    · rw [Category.assoc, Category.assoc, hℓs, ← Category.assoc, Over.w]
      simp [Over.w]

private theorem bridge [IsIso f] (n : QMap o u₁ f c) (n' : QMap o u₂ (f ≫ g) c) :
    ∃ m : ObjMap u₁ u₂ g, n'.φ = n.φ ≫ m.φ := by
  haveI hiso : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  have hinvw : inv n.φ ≫ o.A.hom = u₁.A.hom ≫ inv f := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, n.cart.1.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv : IsGrpPullback u₁.A o.A (inv f) (inv n.φ) :=
    IsGrpPullback.cancel n.cart
      (IsGrpPullback.congr (GlobalTheory.EndLoc.isGrpPullback_id u₁.A) (by simp) (by simp)) hinvw
  have hcart : IsGrpPullback u₁.A u₂.A g (inv n.φ ≫ n'.φ) :=
    IsGrpPullback.congr (IsGrpPullback.comp hinv n'.cart) (by simp) rfl
  obtain ⟨ψ₂, hψ⟩ := MapComp.exists_isSquare (G := o.A) (G' := u₁.A) hinvw
  have hid : Geo.Tor.IsSquare (𝟙 u₁.A.left) (𝟙 (u₁.A ⊗ u₁.A).left) := by
    constructor <;> simp
  have hψn : ψ₂ ≫ n.φ₂ = 𝟙 _ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hψ n.sq)
    rw [IsIso.inv_hom_id]
    exact hid
  refine ⟨⟨inv n.φ ≫ n'.φ, ψ₂ ≫ n'.φ₂, hcart, MapComp.isSquare_comp hψ n'.sq, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hx : Over.Hom.left (u₁.act.act x) ≫ inv n.φ = inv n.φ ≫ Over.Hom.left (o.act.act x) := by
      rw [IsIso.comp_inv_eq, Category.assoc, n.act x, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hx, Category.assoc, n'.act x, Category.assoc]
  · exact LBIso.trans u₁.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
      (GlobalTheory.SiegLower.lbIso_pull_id u₁.isLB)
      (LBIso.trans (pull_isLB u₁.isLB _) (pull_isLB o.isLB _) (pull_isLB u₂.isLB _)
        (MapComp.lbIso_pull_comp n.pol ψ₂ hψn.symm).symm
        (MapComp.lbIso_pull_comp n'.pol ψ₂ rfl))
  · intro y
    have hy : Over.Hom.left (u₁.eta y) = inv f ≫ Over.Hom.left (o.eta (c • y)) ≫ n.φ := by
      rw [n.eta y, IsIso.inv_hom_id_assoc]
    rw [hy]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, n'.eta y, IsIso.inv_hom_id_assoc]
  · simp

end UpperTheory.Gal.Int.Geo.QCompPf

open UpperTheory.Gal.Int.Geo.QCompPf in
theorem UpperTheory.quotient_map_comp : QComp := by
  intro q _ D R R' _ _ _ b gb N N₀ c X X₁ X₂ s s₁ s₂ o u₁ u₂ f g
  refine ⟨fun n m => ⟨after n m, rfl⟩, fun n' m => factor n' m, fun hf n n' => bridge n n', ?_⟩
  intro X' s' o' e m n
  exact ⟨before m n, rfl⟩
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.ActionSupremumCommute

variable {A O M : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup M] [Module O M]

private lemma nat_act (N : ℕ) (y : M) : algebraMap A O (N : A) • y = N • y := by
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

private lemma act_comm (c d : A) (y : M) :
    algebraMap A O c • algebraMap A O d • y = algebraMap A O d • algebraMap A O c • y := by
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm c d]

private lemma exists_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) :
    ∃ r s : A, b = r * a + s * (N : A) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  exact ⟨r, s, rfl⟩

private lemma act_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) (w : M) :
    ∃ y z : M, algebraMap A O b • w = algebraMap A O a • y + N • z := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • w, algebraMap A O s • w, ?_⟩
  rw [map_add (f := _), add_smul, map_mul, map_mul, mul_smul, mul_smul, act_comm r a, act_comm s (N : A), nat_act]

private lemma act_sup_of {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)})
    {y z : M} (hy : algebraMap A O a • y = N • z) :
    ∃ z' : M, algebraMap A O b • y = N • z' := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • z + algebraMap A O s • y, ?_⟩
  rw [map_add (f := _), add_smul, map_mul, map_mul, mul_smul, mul_smul, hy, nat_act, smul_add,
    smul_comm N (algebraMap A O r) z, smul_comm N (algebraMap A O s) y]

private lemma fwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) (W : Submodule O M)
    (hW : ∀ c ∈ 𝔞, ∀ z : M, algebraMap A O c • z ∈ W) {y z : M}
    (hy : algebraMap A O a • y = N • z) : y ∈ W := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ u ∈ W, algebraMap A O t • y = N • u := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z', hz'⟩ := act_sup_of hb hy
      refine ⟨algebraMap A O c • z', hW c hc z', ?_⟩
      rw [mul_comm b c, map_mul, mul_smul, hz']
      exact smul_comm _ _ _
    · rintro t t' ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      exact ⟨u + v, W.add_mem hu hv, by rw [map_add (f := _), add_smul, hu', hv', smul_add]⟩
  obtain ⟨u, hu, hu'⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hu'
  rwa [inj y u hu']

private lemma bwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)}) {y : M}
    (hy : y ∈ Submodule.span O {z : M | ∃ c ∈ 𝔞 ^ 1, ∃ z' : M, z = algebraMap A O c • z'}) :
    ∃ z : M, algebraMap A O a • y = N • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [pow_one] at hc
    have hac : a * c ∈ Ideal.span {(N : A)} :=
      h ▸ Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hac
    refine ⟨algebraMap A O t • z', ?_⟩
    rw [← mul_smul, ← map_mul, ← ht, map_mul, mul_smul, act_comm t (N : A), nat_act]
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hx'
    exact ⟨u + v, by rw [smul_add, hu, hv, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o • u, ?_⟩
    rw [← mul_smul, Algebra.commutes, mul_smul, hu]
    exact smul_comm _ _ _

private lemma part2 {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) {x : M}
    (hx : ∀ c ∈ 𝔞, ∃ z : M, algebraMap A O c • x = N • z) :
    ∃ y z : M, x = algebraMap A O a • y + N • z := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ y z : M, algebraMap A O t • x = N • (algebraMap A O a • y + N • z) := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z0, hz0⟩ := hx c hc
      obtain ⟨y, z, hyz⟩ := act_sup (O := O) hb z0
      refine ⟨y, z, ?_⟩
      rw [map_mul, mul_smul, hz0, ← hyz]
      exact smul_comm _ _ _
    · rintro t t' ⟨y, z, h1⟩ ⟨y', z', h2⟩
      refine ⟨y + y', z + z', ?_⟩
      rw [map_add (f := _), add_smul, h1, h2]
      simp only [smul_add]
      abel
  obtain ⟨y, z, hyz⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hyz
  exact ⟨y, z, inj _ _ hyz⟩

end UpperTheory.ActionSupremumCommute

theorem UpperTheory.lattice_generation :
    LatGen := by
  intro q _ D a N 𝔞 hN hG
  haveI := D.freeLa
  have inj : ∀ u v : D.La, N • u = N • v → u = v := by
    intro u v huv
    have h0 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, huv, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd (Int.natCast_eq_zero.mp h1) hN.ne'
    · exact sub_eq_zero.mp h1
  refine ⟨fun y => ⟨fun ⟨z, hz⟩ => UpperTheory.ActionSupremumCommute.fwd hG inj _ ?_ hz,
    fun hy => UpperTheory.ActionSupremumCommute.bwd hG hy⟩, fun x hx => UpperTheory.ActionSupremumCommute.part2 hG inj hx⟩
  intro c hc z
  exact Submodule.subset_span ⟨c, by rwa [pow_one], z, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.LevelActionGenerator

variable {X : Scheme.{0}}

private theorem pb_mul {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} (x y : T ⟶ A) :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 X) ≅ T := Over.isoMk (Iso.refl _) (by simp)
  have he : e.hom.left = 𝟙 _ := rfl
  have key := h.2 T x y (e.hom ≫ x ≫ f) (e.hom ≫ y ≫ f)
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
  rw [← MonObj.comp_mul, Over.comp_left, he, Category.id_comp] at key
  apply Over.OverMorphism.ext
  rw [key, Over.comp_left, hf]

private theorem pb_one {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} :
    (1 : T ⟶ A) ≫ f = 1 := by
  have h1 := pb_mul h f hf (1 : T ⟶ A) 1
  rw [_root_.mul_one] at h1
  simpa using h1

private theorem act_nat {O : Type} [Ring O] {A : Over X} [GrpObj A] [IsCommMonObj A] (act : OActN O A) {T : Over X}
    (u : T ⟶ A) (m : ℕ) : u ≫ act.act (m : O) = u ^ m := by
  induction m with
  | zero =>
    have h0 : act.act (0 : O) = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      simpa using this
    rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
  | succ m ih =>
    rw [Nat.cast_succ, act.add, act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

private theorem gen_mem {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hm : (N : A) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 := by
    rw [h']
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.mul_le_right (I := Ideal.span {a} ⊔ Ideal.span {(N : A)}) (J := 𝔞)) hm

end UpperTheory.LevelActionGenerator

open UpperTheory.LevelActionGenerator in
theorem UpperTheory.quotient_level_of_lattice_generation :
    LatGen → QLev := by
  intro hLat q _ D R R' _ _ _ b gb N N₀ c a 𝔞 hN hgen X s s₀ o o₀ n
  have hw : n.φ ≫ o₀.A.hom = o.A.hom := by simpa using n.cart.1.w
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  let f : o.A ⟶ o₀.A := Over.homMk n.φ hw
  let g : o₀.A ⟶ o.A := Over.homMk (inv n.φ) (by rw [IsIso.inv_comp_eq, hw])
  have hfl : f.left = n.φ := rfl
  have hfg : f ≫ g = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hgf : g ≫ f = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hinj : ∀ {T : Over X} (u v : T ⟶ o.A), u ≫ f = v ≫ f → u = v := by
    intro T u v huv
    have := congrArg (· ≫ g) huv
    simpa [Category.assoc, hfg] using this
  have hmul : ∀ {T : Over X} (u v : T ⟶ o.A), (u * v) ≫ f = (u ≫ f) * (v ≫ f) :=
    fun u v => pb_mul n.cart f hfl u v
  have hone : ∀ {T : Over X}, (1 : T ⟶ o.A) ≫ f = 1 := pb_one n.cart f hfl
  have hone' : ∀ {T : Over X}, (1 : T ⟶ o₀.A) ≫ g = 1 := by
    intro T
    apply hinj
    rw [Category.assoc, hgf, Category.comp_id, hone]
  have hact : ∀ c' : D.O, o.act.act c' ≫ f = f ≫ o₀.act.act c' := by
    intro c'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact n.act c'
  have e_add : ∀ u v : D.La, o.eta (u + v) = o.eta u * o.eta v := fun u v => o.eta_add u v
  have e_lin : ∀ (c' : D.O) (u : D.La), o.eta (c' • u) = o.eta u ≫ o.act.act c' :=
    fun c' u => o.eta_lin c' u
  have e_ker : ∀ u : D.La, o.eta (N • u) = 1 := fun u => o.eta_ker u
  obtain ⟨hL1, hL2⟩ := hLat q D a N 𝔞 hN hgen
  refine ⟨fun y => o.eta (algebraMap (𝓞 D.F) D.O a • y) ≫ f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y z
    simp only
    rw [smul_add, e_add, hmul]
  · intro c' y
    simp only
    have hcomm : algebraMap (𝓞 D.F) D.O a • (c' • y) = c' • (algebraMap (𝓞 D.F) D.O a • y) := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    rw [hcomm, e_lin, Category.assoc, hact, Category.assoc]
  · intro y hy
    obtain ⟨z, hz⟩ := (hL1 y).2 hy
    simp only
    rw [hz, e_ker, hone]
  · intro k _ _ x
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o.geom k x _ hβ
    have hI' : ∀ y : D.La, toUnit (Over.mk x) ≫ o.eta y = I.ev N y := fun y => hI y
    have I_add : ∀ u v : D.La, I.ev N (u + v) = I.ev N u * I.ev N v := fun u v => I.add N u v
    have I_lin : ∀ (c' : D.O) (u : D.La), I.ev N (c' • u) = I.ev N u ≫ o.act.act c' :=
      fun c' u => I.lin N c' u
    have I_ker : ∀ u : D.La, I.ev N u = 1 ↔ ∃ v : D.La, u = N • v := fun u => I.ker N hN u
    have I_onto : ∀ r : Over.mk x ⟶ o.A, r ^ N = 1 ↔ ∃ u : D.La, I.ev N u = r :=
      fun r => I.onto N hN r
    constructor
    · intro y hy
      simp only at hy
      rw [← Category.assoc, ← hone] at hy
      have h1 := hinj _ _ hy
      rw [hI'] at h1
      obtain ⟨z, hz⟩ := (I_ker _).1 h1
      exact (hL1 y).1 ⟨z, hz⟩
    · intro g₀ hg₀
      have hg'act : ∀ c' : D.O, (g₀ ≫ g) ≫ o.act.act c' = (g₀ ≫ o₀.act.act c') ≫ g := by
        intro c'
        apply hinj
        simp only [Category.assoc, hact, reassoc_of% hgf, hgf, Category.comp_id]
      have hkill : ∀ c' ∈ 𝔞, (g₀ ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c') = 1 := by
        intro c' hc'
        rw [hg'act, hg₀ c' (by rwa [pow_one]), hone']
      have hpow : (g₀ ≫ g) ^ N = 1 := by
        have hn := act_nat o.act (g₀ ≫ g) N
        have hc : ((N : ℕ) : D.toG.O) = algebraMap (𝓞 D.F) D.O (N : 𝓞 D.F) := (map_natCast _ N).symm
        rw [hc] at hn
        rw [← hn]
        exact hkill _ (gen_mem hgen)
      obtain ⟨x', hx'⟩ := (I_onto (g₀ ≫ g)).1 hpow
      have hcond : ∀ c' ∈ 𝔞, ∃ z : D.La, algebraMap (𝓞 D.F) D.O c' • x' = N • z := by
        intro c' hc'
        apply (I_ker _).1
        rw [I_lin, hx']
        exact hkill c' hc'
      obtain ⟨y, z, hyz⟩ := hL2 x' hcond
      refine ⟨y, ?_⟩
      have hyI : toUnit (Over.mk x) ≫ o.eta (algebraMap (𝓞 D.F) D.O a • y) = g₀ ≫ g := by
        rw [hI', ← hx', hyz, I_add, (I_ker (N • z)).2 ⟨z, rfl⟩, _root_.mul_one]
      simp only
      rw [← Category.assoc, hyI, Category.assoc, hgf, Category.comp_id]
  · intro y
    rfl
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open UpperTheory.Gal.Int.Geo

private theorem unit_aux {A : Type} [CommRing A] {m c t t' s : A} (hm : m = c * t) (ht : t * t' = 1)
    (hs : m * s = 1) : c = 1 * (m * t') ∧ (m * t') * (t * s) = 1 := by
  constructor
  · rw [_root_.one_mul, hm, _root_.mul_assoc, ht, _root_.mul_one]
  · calc (m * t') * (t * s) = (m * s) * (t * t') := by ring
      _ = 1 := by rw [hs, ht, _root_.one_mul]

theorem UpperTheory.trace_unit_of_pullback_multiplier :
    TrBack → MultUnit → TrUnit := by
  intro hB hM p _ D G L R _ _ gb h X s N' N o' o ψ hT hh
  obtain ⟨ψ', -, e₁, e₂⟩ := hB p D G L R gb h X s N' N o' o ψ hT 1 (Nat.coprime_one_left p)
    (fun v hv => ⟨L.actG h⁻¹ v, integ_of_mem (inv_mem hh) v hv, by
      rw [one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩)
  have hiso : CategoryTheory.IsIso ψ := ⟨ψ', e₁.trans (pow_one _), e₂.trans (pow_one _)⟩
  refine ⟨hiso, ?_⟩
  obtain ⟨-, -, -, ⟨c, hc, hP, t, t', ht, ht', htt, hm⟩, -⟩ := hT
  obtain ⟨hu, hfix⟩ := hM p D G L
  obtain ⟨s', hi, hs, hs1⟩ := hu h hh
  obtain ⟨a₁, a₂⟩ := unit_aux hm htt hs1
  have hint : ∀ {a b : GlobalTheory.LKTrip.AfP p}, GlobalTheory.LKGeo.IsIntAf a → GlobalTheory.LKGeo.IsIntAf b → GlobalTheory.LKGeo.IsIntAf (a * b) := fun ha hb v => by
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  have hc1 : c = 1 := hfix c 1 _ _ hc (Nat.coprime_one_left p) (hint hi ht') (hint ht hs) a₂
    (by rw [Nat.cast_one]; exact a₁)
  subst hc1
  exact hP
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGenericModuliPoint
set_option autoImplicit false

namespace UpperTheory

open UpperTheory.Gal.Int.Geo

theorem exists_generic_moduli_point : GenEx := by
  intro A _ _ _ 𝔞 N hN
  have hN0 : (N : A) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨fun hmem => ?_, fun a t h => ?_⟩
  · have hdvd : 𝔞 ∣ Ideal.span {(N : A)} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    obtain ⟨𝔟, h𝔟⟩ := hdvd
    have hle : Ideal.span {(N : A)} ≤ 𝔟 := by
      rw [h𝔟]; exact Ideal.mul_le_right
    have hne : Ideal.span {(N : A)} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hN0
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    refine ⟨a, ?_⟩
    unfold IsGen
    rw [sup_comm, ha, mul_comm, ← h𝔟]
  · unfold IsGen at h ⊢
    have hs : Ideal.span {(t : A) * a} ⊔ Ideal.span {((N * t : ℕ) : A)}
        = Ideal.span {(t : A)} * (Ideal.span {a} ⊔ Ideal.span {(N : A)}) := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]
    rw [hs, mul_assoc, h, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]

end UpperTheory
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem UpperTheory.quotient_moduli_iso : UpperTheory.Gal.Int.Geo.QIso := by
  intro q _ D R R' _ _ _ b gb N N' N₀ c c' X X₁ s s₁ o' o u f ψ hiso hmon hact hpol heta n
  obtain ⟨hP⟩ := hpol
  have hrefl : ∀ {Y : Scheme} (L : LB Y), L.IsLB → LBIso L L :=
    fun L hL => (GlobalTheory.CechPic.cls_eq_iff hL hL).mp rfl
  have h1 : (Hecke.lbPow o'.P 1).IsLB := DVR.linComb_isLB _ o'.isLB _ _
  have e1 : LBIso o'.P (Hecke.lbPow o'.P 1) :=
    (GlobalTheory.CechPic.cls_eq_iff o'.isLB h1).mp (by simpa only [one_smul] using (GlobalTheory.LocTrivDescent.cls_lbPow_eq o'.isLB 1 h1).symm)
  have e3 : LBIso (o.P.pull (Hecke.sq2 ψ)) ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) n.pol
  have e4 : LBIso ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn u.P (fun _ => n.φ₂) (fun _ => (1 : ℤ)) (Hecke.sq2 ψ))
      (hrefl _ (pull_isLB (pull_isLB u.isLB _) _))
  have pol : LBIso o'.P (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u.isLB _)
      (LBIso.trans o'.isLB h1 (pull_isLB o.isLB _) e1 hP)
      (LBIso.trans (pull_isLB o.isLB _) (pull_isLB (pull_isLB u.isLB _) _) (pull_isLB u.isLB _) e3 e4)
  refine ⟨⟨Over.Hom.left ψ ≫ n.φ, Hecke.sq2 ψ ≫ n.φ₂, ?_, ?_, ?_, pol, ?_⟩, rfl⟩
  · have hc := (GlobalTheory.FibreAct.isGrpPullback_of_iso ψ).comp n.cart
    simpa using hc
  · constructor
    · rw [Category.assoc, n.sq.1, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_fst, Over.comp_left]
    · rw [Category.assoc, n.sq.2, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_snd, Over.comp_left]
  · intro x
    rw [← Category.assoc, ← Over.comp_left, hact x, Over.comp_left, Category.assoc, n.act x,
      Category.assoc]
  · intro y
    rw [← Category.assoc, ← Over.comp_left, heta y, n.eta y]
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

private theorem sec_eq_of_points {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (σ σ' : 𝟙_ (Over X) ⟶ A) (h₁ : σ ^ n = 1) (h₂ : σ' ^ n = 1)
    (hpt : ∀ q : X, ∃ (k : Type) (_ : Field k) (y : Sp k ⟶ X), q ∈ Set.range y ∧
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ') : σ = σ' := by
  have key : ∀ q : X, ∃ V : X.Opens, q ∈ V ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
    intro q
    obtain ⟨k, hk, y, ⟨z, hz⟩, he⟩ := hpt q
    obtain ⟨V, hV, hVe⟩ := GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point X A hA n hn σ σ' h₁ h₂ k y he
    exact ⟨V, hV ⟨z, hz⟩, hVe⟩
  choose V hV hVe using key
  have hcov : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun q _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hV q⟩
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover V hcov) _ _ fun q => hVe q

private theorem map_nsmul_pow {M Q : Type} [AddCommGroup M] [Group Q] (f : M → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (m : ℕ) (a : M) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ m ih =>
    rw [succ_nsmul, hf, ih, pow_succ]

private theorem pow_comp_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} [GrpObj A] [GrpObj B]
    (a : T ⟶ A) (ψ : A ⟶ B) [IsMonHom ψ] (m : ℕ) : (a ≫ ψ) ^ m = (a ^ m) ≫ ψ := (map_pow (IsMonHom.monoidHom ψ T) a m).symm

private theorem ev_tower {G : GDatum} {k Q : Type} [Field k] [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) {M n c : ℕ} (hM : M = n * c) (hn : 0 < n) (hc : 0 < c) (z : G.La) :
    I.ev M (c • z) = I.ev n z := by
  subst hM
  rw [map_nsmul_pow (I.ev _) (I.add _)]
  exact I.tower n c hn hc z

theorem UpperTheory.trace_eta_identity : UpperTheory.Gal.Int.Geo.TrEta := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT n c' c hN' hN x y hxy
  haveI : IsMonHom ψ := hT.1
  have h3' := N'.2.1
  have h3 := N.2.1
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hN'; omega)
  have hc' : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN'; omega)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN; omega)
  have hcop : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c', hN'⟩ N'.2.2
  have hunit : IsUnit (n : Γ(X, ⊤)) := by
    have hR : IsUnit (n : R) := by
      have hq : IsUnit (n : ℚ) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
      simpa using hq.map (algebraMap ℚ R)
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  have ex' : (n • c' • x : D.La) = (↑N' : ℕ) • x := by rw [smul_smul, ← hN']
  have ex : (n • c • y : D.La) = (↑N : ℕ) • y := by rw [smul_smul, ← hN]
  have e1 : (o'.eta (c' • x)) ^ n = 1 :=
    (map_nsmul_pow o'.eta o'.eta_add n (c' • x)).symm.trans ((congrArg o'.eta ex').trans (o'.eta_ker x))
  have hpow1 : (o'.eta (c' • x) ≫ ψ) ^ n = 1 :=
    (pow_comp_hom _ _ _).trans ((congrArg (· ≫ ψ) e1).trans (map_one (IsMonHom.monoidHom ψ _)))
  have hpow2 : (o.eta (c • y)) ^ n = 1 :=
    (map_nsmul_pow o.eta o.eta_add n (c • y)).symm.trans ((congrArg o.eta ex).trans (o.eta_ker y))
  refine sec_eq_of_points o.A o.ab n hunit _ _ hpow1 hpow2 (fun q => ?_)
  let κ := X.residueField q
  let k := AlgebraicClosure κ
  let y0 : Sp k ⟶ X := spMap (algebraMap κ k) ≫ X.fromSpecResidueField q
  let β : R →+* k := (Spec.preimage (y0 ≫ s)).hom
  have hβ : y0 ≫ s = spMap β := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (y0 ≫ s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', I'', hI', hI'', hiff⟩ := hT.2.2.2.2 k y0 β hβ
  refine ⟨k, inferInstance, y0, ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply q _⟩, ?_⟩
  calc toUnit (Over.mk y0) ≫ (o'.eta (c' • x) ≫ ψ)
      = (toUnit (Over.mk y0) ≫ o'.eta (c' • x)) ≫ ψ := (Category.assoc _ _ _).symm
    _ = I'.ev (↑N') (c' • x) ≫ ψ := congrArg (· ≫ ψ) (hI' _)
    _ = I'.ev n x ≫ ψ := congrArg (· ≫ ψ) (ev_tower I' hN' hn hc' x)
    _ = I''.ev n y := (hiff n hn hcop x y).mpr hxy
    _ = I''.ev (↑N) (c • y) := (ev_tower I'' hN hn hc y).symm
    _ = toUnit (Over.mk y0) ≫ o.eta (c • y) := (hI'' _).symm
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralGeometricGaloisSplitting
open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.integralGeometricGalois_splitting : UpperTheory.Gal.Int.Geo.SplitOf := by
  intro W X c _ _ Δ _ a ha h
  refine UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts c c Δ a ha ?_
  intro Ω _ _ x y hy
  obtain ⟨δ, hδ, hu⟩ := h Ω x y hy.symm
  exact ⟨δ, hδ.symm, fun δ' hδ' => hu δ' hδ'.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNumberFieldPointOfGeneric
open UpperTheory.Gal.Int.Geo
open NumberField

private lemma natDvd_of_eq_mul {F : Type} [Field F] [NumberField F] {n m : ℕ} {x : 𝓞 F}
    (h : (n : 𝓞 F) * x = (m : 𝓞 F)) : n ∣ m := by
  have hd : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  have hn := congrArg (Algebra.norm ℤ) h
  have e : ∀ k : ℕ, (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := fun k => by simp
  rw [map_mul, e n, e m, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at hn
  have hdvd : (n : ℤ) ^ Module.finrank ℤ (𝓞 F) ∣ (m : ℤ) ^ Module.finrank ℤ (𝓞 F) :=
    ⟨_, hn.symm⟩
  exact Int.natCast_dvd_natCast.1 ((Int.pow_dvd_pow_iff hd).1 hdvd)

theorem UpperTheory.exists_number_field_point_of_generic :
    GenEx → NumEx := by
  intro hG p _ D E _ _ gb w q _ r 𝔴 𝔫 S N hN
  refine ⟨fun hmem => ?_, fun c a t h => ?_⟩
  · rw [S.lev] at hmem
    obtain ⟨x, hx, hxe⟩ := Ideal.mem_span_singleton_mul.1 hmem
    have hNa : (N : 𝓞 D.F) ∈ S.𝔞 := hxe ▸ Ideal.mul_mem_left _ _ hx
    obtain ⟨a, ha⟩ := (hG (𝓞 D.F) S.𝔞 N hN).1 hNa
    obtain ⟨c, hc⟩ := natDvd_of_eq_mul hxe
    exact ⟨c, a, hc, ha⟩
  · exact ⟨by rw [h.1, mul_assoc], (hG (𝓞 D.F) S.𝔞 N hN).2 a t h.2⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerInvariantOfBaseInvariantPowerCartesian
open UpperTheory.Gal.Int.Geo
open CategoryTheory AlgebraicGeometry

private theorem powMap_congr {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f f' : S' ⟶ S} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ h k = GlobalTheory.KS.powMap f' φ' h' k := by
  subst hf hφ
  rfl

theorem UpperTheory.tower_invariant_of_base_invariant_powerCartesian :
    BaseInv → PowCart → PiInv := by
  intro hB hP p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu x y
  obtain ⟨π, o, ψ, φ, hw, ov, tr, e⟩ := T.tr_eq N' N u x y
  obtain ⟨h1, h2⟩ := hB p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu
    ⟨π, o, ψ, φ, ov, tr⟩
  have h1' : π ≫ C.j = C'.j := h1
  have h2' : (ψ.left ≫ φ.φ) ≫ C.m.φ = C'.m.φ := by
    rw [Category.assoc]; exact h2
  have hv := C.m.cart.1.w
  have hw' : ((ψ.left ≫ φ.φ) ≫ C.m.φ) ≫ S.Y.univ.A.hom = (T.M N').univ.A.hom ≫ π ≫ C.j := by
    rw [Category.assoc, hv, ← Category.assoc, hw, Category.assoc]
  have hc := (hP _ _ _ (T.M N').univ.A (T.M N).univ.A S.Y.univ.A π C.j (ψ.left ≫ φ.φ) C.m.φ hw hv k).2.2 hw'
  simp only [Site.pi, Cls.pw]
  rw [← Category.assoc, e, Category.assoc, hc]
  exact congrArg _ (powMap_congr h1' h2' _ _ k)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringCongruenceOfHeckeLies
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_covering_congruence_of_hecke_lies :
    MIn → SiteEx → NumEx → ClsEx → KSCover → TjLies → KSCong := by
  intro hM hS hN hC hV hL p _ D G L hsc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ϑ hG
  obtain ⟨q, r, 𝔫, K₀, hat, hok, hlev, hKN, hNn, hdeck, hall⟩ := hG
  haveI : Fact q.Prime := ⟨hat.prime⟩
  haveI : 𝔴.IsMaximal := hat.max
  obtain ⟨S⟩ := hS p D G hsc E e gb hstd w q r 𝔴 𝔫 hpl hat hok
  have hNpos : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  obtain ⟨c, a, hnum⟩ := (hN p D E gb w q r 𝔴 𝔫 S N.1 hNpos).1 hNn
  obtain ⟨⟨C⟩, -⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat N.1 S.N₀ c a S.𝔞
    hnum.1 hNpos S.std.three S.std.cop hnum.2 S.Y (T.M N).X (T.M N).s (T.M N).univ
  obtain ⟨Cv⟩ := hV p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J A g θ hdeck
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  haveI := S.et
  obtain ⟨Tc, Lc, d, h, hov, hpt⟩ := hM.cong q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M ϖ hϖ S.𝔞 1
    S.sup S.upow S.Y S.π S.ov inferInstance S.mπ k
  choose γ hγK hγT hγd hγr hγθ using hall
  refine ⟨Cv.toCover, q, S.f, hat.prime, S.qmem, S.norm, ϖ, fun j => (h j).corr,
    fun j => γ j (Nat.lt_succ_iff.1 j.2), fun j => (L.KN (g (γ j (Nat.lt_succ_iff.1 j.2))).M.1).relIndex
      (K₀ ⊓ K₀.comap (MulAut.conj (g (γ j (Nat.lt_succ_iff.1 j.2))).h).toMonoidHom), hϖ, hpt, fun j => ⟨hov j, ?_, ?_⟩⟩
  · obtain ⟨h0, κ, e1, e2, e3⟩ := hL p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J g _ j
      (Nat.lt_succ_iff.1 j.2) (hγK _ _) (hγT _ _) (hγd _ _) (hγr _ _) (Tc j) (Lc j)
    exact ⟨h0, κ, e1, e2, e3⟩
  · exact hγθ _ _
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaPointwise
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.trace_eta_pointwise : TrEtaPt := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  have hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom := by
    simp [spMap, Spec.map_preimage]
  obtain ⟨I', I'', h1, h2, h3⟩ := hgeo Ω z _ hz
  have hpos : ∀ M : Lv p, 0 < (M : ℕ) := fun M => by
    have := M.2.1
    omega
  have hzero : ∀ n : ℕ, I''.ev n 0 = 1 := fun n => by
    have h := I''.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hin0 : inAf D 0 = 0 := by
    simp [inAf]
  have e1 := congrArg (· ≫ ψ) (h1 x)
  simp only [Category.assoc] at e1
  refine ⟨?_, ?_⟩
  · refine Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)
    · rw [e1]
      first
        | simp only [hzero]
        | erw [hzero]
    · simp only [hin0, zero_add]
  · rintro rfl y hxy
    refine (h3 _ (hpos N') N'.2.2 x y).mp ?_
    rw [← e1, hxy]
    exact h2 y
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RationalSplittingExists
open UpperTheory.Gal.Int.Geo

private theorem matrix_unique_algEquiv (R A m : Type) [CommSemiring R] [Semiring A] [Algebra R A]
    [fm : Fintype m] [dm : DecidableEq m] [Unique m] : Nonempty (Matrix m m A ≃ₐ[R] A) := by
  refine ⟨{ toFun := fun M => M default default
            invFun := fun a => Matrix.of fun _ _ => a
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            map_add' := ?_
            commutes' := ?_ }⟩
  · intro M
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  · intro a
    simp
  · intro M N
    simp [Matrix.mul_apply]
  · intro M N
    simp
  · intro r
    simp [Matrix.algebraMap_matrix_apply]

open scoped TensorProduct in
theorem UpperTheory.rational_splitting_exists :
    SplitQ := by
  intro p _ D hm q _
  haveI : Unique (Fin D.m) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.2; simp; omega) }
  let e0 : D.O ≃ₐ[NumberField.RingOfIntegers D.F] NumberField.RingOfIntegers D.F :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨D.algebraMap_injective hm, GlobalTheory.T.integers_surjective_of_rank_one p D hm⟩).symm
  exact ⟨(Algebra.TensorProduct.congr e0 AlgEquiv.refl).trans
    (matrix_unique_algEquiv _ _ _).some.symm⟩
end

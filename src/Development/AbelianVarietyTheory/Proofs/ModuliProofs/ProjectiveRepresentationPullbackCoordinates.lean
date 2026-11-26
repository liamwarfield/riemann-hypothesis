module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem r_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  have : (homOfLE h).op = 𝟙 _ := rfl
  simp only [resG, this, CategoryTheory.Functor.map_id]; rfl

theorem r_appLE (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V) (a : Γ(X, U)) :
    resG Y h ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← f.appLE_map e (homOfLE h).op]; rfl

theorem appLE_r (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(X, U')) :
    (f.appLE U V e).hom (resG X h a) = (f.appLE U' V (e.trans (fun _ hy => h hy))).hom a := by
  rw [← f.map_appLE e (homOfLE h).op]; rfl

theorem appLE_appLE (f : Z ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = ((f ≫ g).appLE U W e).hom a := by
  rw [← Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂]; rfl

theorem pull_le (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j PUnit.unit) :=
  LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit

theorem le_pull (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : f ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull f).U j :=
  fun _ h => Set.mem_iInter.2 fun _ => h

theorem pull_g (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (e : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    ((M.pull f).g j j').val = (f.appLE _ _ e).hom (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  show ((∏ _k : PUnit, (res e (pullU f _ (M.g (j PUnit.unit) (j' PUnit.unit)))) ^ (1 : ℤ) :
    Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem pull_inf_le (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι) :
    (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :=
  fun _ h => ⟨pull_le M f j h.1, pull_le M f j' h.2⟩

def secPull (M : LB X) (f : Y ⟶ X) (s : M.Sec) : (M.pull f).Sec where
  f j := (f.appLE _ _ (pull_le M f j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h := congrArg (f.appLE _ _ (pull_inf_le M f j j')).hom (s.compat (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul] at h
    erw [← pull_g M f j j'] at h
    erw [appLE_r, appLE_r] at h
    erw [r_appLE, r_appLE]
    exact h

theorem isGen_val {L : LB X} (t : L.Gen) : t.IsGen ↔ ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i).val =
    (L.g i j).val * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j).val :=
  forall₂_congr fun _ _ => Units.ext_iff

theorem le₁ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J : PUnit → PUnit → M.ι) :
    ((M.pull π).pull x).U J ≤ (M.pull (x ≫ π)).U (J PUnit.unit) :=
  fun _ h => le_pull M (x ≫ π) _ (pull_le M π _ (pull_le (M.pull π) x J h))

theorem le₂ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (j : PUnit → M.ι) :
    (M.pull (x ≫ π)).U j ≤ ((M.pull π).pull x).U (fun _ => j) :=
  fun _ h => le_pull (M.pull π) x (fun _ => j) (le_pull M π _ (pull_le M (x ≫ π) j h))

theorem pullpull_g (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J J' : PUnit → PUnit → M.ι)
    (e : ((M.pull π).pull x).U J ⊓ ((M.pull π).pull x).U J' ≤
      (x ≫ π) ⁻¹ᵁ (M.U (J PUnit.unit PUnit.unit) ⊓ M.U (J' PUnit.unit PUnit.unit))) :
    (((M.pull π).pull x).g J J').val =
      ((x ≫ π).appLE _ _ e).hom (M.g (J PUnit.unit PUnit.unit) (J' PUnit.unit PUnit.unit)).val := by
  rw [pull_g (M.pull π) x J J' (pull_inf_le _ _ _ _), pull_g M π _ _ (pull_inf_le _ _ _ _)]
  exact appLE_appLE x π _ _ e _

theorem secCoord_pull {σ : Type} (M : LB X) (th : σ → M.Sec) (π : Y ⟶ X) {T : Type} [CommRing T] (x : Sp T ⟶ Y)
    (v : σ → T) : SecCoord (M.pull π) (fun i => secPull M π (th i)) x v ↔ SecCoord M th (x ≫ π) v := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun j => res (le₂ M π x j) (τ.s fun _ => j)⟩, (isGen_val _).2 fun j j' => ?_, fun i j e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₂ M π x j) (le₂ M π x j')))
        ((isGen_val τ).1 hτ (fun _ => j) (fun _ => j'))
      rw [map_mul] at h0
      erw [pullpull_g M π x (fun _ => j) (fun _ => j') ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _)),
        rr, r_appLE] at h0
      erw [pull_g M (x ≫ π) j j' (pull_inf_le _ _ _ _)]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₂ M π x j') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₂ M π x j)) (h i (fun _ => j) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ _ e _).symm.trans h0
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun J => res (le₁ M π x J) (τ.s (J PUnit.unit))⟩, (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₁ M π x J) (le₁ M π x J')))
        ((isGen_val τ).1 hτ (J PUnit.unit) (J' PUnit.unit))
      rw [map_mul] at h0
      erw [pull_g M (x ≫ π) (J PUnit.unit) (J' PUnit.unit) (pull_inf_le _ _ _ _), rr, r_appLE] at h0
      erw [pullpull_g M π x J J' ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _))]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₁ M π x J') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₁ M π x J)) (h i (J PUnit.unit) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ e _ _).trans h0

theorem projRep_baseChange : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  intro R R' σ _ _ φ I Z Z' s s' π M th ⟨hM, hloc, hpts⟩ hp
  refine ⟨fun i => secPull M π (th i), ⟨pull_isLB hM π, fun T _ β x v hx hv => ?_, fun T _ β v hu hF => ?_⟩,
    fun T _ x v => secCoord_pull M th π x v⟩
  · have hs : (x ≫ π) ≫ s = spMap (β.comp φ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    obtain ⟨h1, h2⟩ := hloc T (β.comp φ) (x ≫ π) v hs ((secCoord_pull M th π x v).1 hv)
    refine ⟨h1, fun F hF => ?_⟩
    have : I.map (MvPolynomial.map φ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      rw [Ideal.map_le_iff_le_comap]
      intro G hG
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact h2 G hG
    exact this hF
  · obtain ⟨y, ⟨hy, hv⟩, huniq⟩ := hpts T (β.comp φ) v hu fun G hG => by
      rw [← MvPolynomial.eval₂_map]
      exact hF _ (Ideal.mem_map_of_mem _ hG)
    have hw : y ≫ s = spMap β ≫ spMap φ := by rw [hy, spMap_comp]
    refine ⟨hp.lift y (spMap β) hw, ⟨hp.lift_snd _ _ _, (secCoord_pull M th π _ v).2 (by rw [hp.lift_fst]; exact hv)⟩, ?_⟩
    rintro x ⟨hx, hxv⟩
    apply hp.hom_ext
    · rw [hp.lift_fst]
      refine huniq _ ⟨?_, (secCoord_pull M th π x v).1 hxv⟩
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    · rw [hp.lift_snd, hx]

end GlobalTheory.ZM.RepBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.projective_representation_pullback_coordinates : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  first | exact @GlobalTheory.ZM.RepBC.projRep_baseChange | exact GlobalTheory.ZM.RepBC.projRep_baseChange | (intros; apply GlobalTheory.ZM.RepBC.projRep_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

abbrev Mc (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)

theorem exists_idem (l : Level H) : ∃ e ∈ Mc l, 1 - e ∈ l.Mb := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  exact ⟨y, hy, by rw [← hxy, add_sub_cancel_right]; exact hx⟩

theorem M_pos (l : Level H) : 0 < l.M := by
  have := l.three_le
  omega

theorem modN_of_mem_span {n : ℕ} {a : D.La}
    (h : a ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN n a := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, -, hb⟩ := h
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem modN_smul_Mb (l : Level H) {c : 𝓞 E} (hc : c ∈ Mc l) {a : D.La}
    (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, mul_comm, l.prod] at h1

theorem modN_smul_Mc (l : Level H) {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb • l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, l.prod] at h1

theorem modN_of_mem_both (l : Level H) {a : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (ha' : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M a := by
  obtain ⟨e, he, he'⟩ := exists_idem l
  obtain ⟨b₁, hb₁⟩ := modN_smul_Mb l he ha
  obtain ⟨b₂, hb₂⟩ := modN_smul_Mc l he' ha'
  refine ⟨b₁ + b₂, ?_⟩
  rw [smul_add, ← hb₁, ← hb₂, ← add_smul]
  simp

theorem nsmul_M_mem (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem add_map_zero {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c) :
    f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)

theorem add_map_nsmul {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; exact add_map_zero hf
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) (a : D.La) :
    I.ev N a ^ (N / n) = I.ev n a := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.tower n (N / n) hn hq a
  rwa [Nat.mul_div_cancel' h] at this

theorem zeta_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) :
    I.ζ N ^ (N / n) = I.ζ n := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.ζ_pow n (N / n) hn hq
  rwa [Nat.mul_div_cancel' h] at this

theorem exists_coprime_zpow {N : ℕ} (hN : 0 < N) {ζ ξ : kˣ} (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) :
    ∃ ν : ℤ, IsCoprime ν (N : ℤ) ∧ ξ = ζ ^ ν := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one (ξ := (ξ : k))
    (by rw [← Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one])
  have hξi : ξ = ζ ^ i := Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
  have hcop : i.Coprime N := (hζ.pow_iff_coprime hN i).1 (by rw [← hξi]; exact hξ)
  exact ⟨i, Nat.isCoprime_iff_coprime.2 hcop, by rw [hξi, zpow_natCast]⟩

theorem exists_adjust
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (l : Level H) (N : ℕ)
    (hM : ∀ ν : ℤ, 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧
      (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      ∀ a, D.ModN l.A (g.f l.A a - a))
    (I : TateIso D k Q act e) (hN : 0 < N) (hA : l.A ∣ N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N)
    (h : ξ ^ (N / l.A) = I.ζ l.A) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La), I'.ev l.M a = I.ev l.M a := by
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hA0 := l.A_pos
  have h1 : I.ζ l.A ^ ν = I.ζ l.A := by
    calc I.ζ l.A ^ ν = ((I.ζ N) ^ (N / l.A)) ^ ν := by rw [zeta_pow_div I hN hA]
      _ = ((I.ζ N) ^ ν) ^ (N / l.A) := by simp only [← zpow_natCast, ← zpow_mul, mul_comm]
      _ = I.ζ l.A := by rw [← hξν, h]
  have hA1 : (l.A : ℤ) ∣ ν - 1 := by
    refine ((I.ζ_prim l.A hA0).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  obtain ⟨g, hgN, -, hgM, hgA⟩ := hM ν hN hνc hA1
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgN
  · rw [LevelTwist.twist_ev]
    exact LevelTwist.ev_congr I hA0 (hgA a)
  · rw [LevelTwist.twist_ev]
    refine LevelTwist.ev_congr I (M_pos l) (modN_of_mem_both l (hgM a) ?_)
    exact Submodule.sub_mem _ (LevelTwist.map_mem_smul_top _ _ ha) ha

theorem exists_of_level
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (N : ℕ)
    (hL : ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (he : ∀ x y c c', e N x y c → e N x y c' → c = c')
    (I : TateIso D k Q act e) (hN : 0 < N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hpow : ∀ a, α a ^ N = 1) (hlin : ∀ c a, α (c • a) = act c (α a))
    (hiso : ∀ a b, e N (α a) (α b) (ξ ^ D.EF a b)) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ ∀ a, I'.ev N a = α a := by
  classical
  choose b hb using fun a => (I.onto N hN (α a)).1 (hpow a)
  let K : Submodule (𝓞 E) D.La := LinearMap.range ((N : 𝓞 E) • LinearMap.id)
  have memK : ∀ x y, I.ev N x = I.ev N y → x - y ∈ K := by
    intro x y hxy
    obtain ⟨z, hz⟩ := (tateIso_ev_eq_iff I hN x y).1 hxy
    exact LinearMap.mem_range.2
      ⟨z, by rw [hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  let β : D.La →ₗ[𝓞 E] D.La ⧸ K :=
    { toFun := fun a => Submodule.Quotient.mk (b a)
      map_add' := fun a c => by
        rw [← Submodule.Quotient.mk_add]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.add, hb, hb, hadd]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.lin, hb, hlin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property K.mkQ β K.mkQ_surjective
  have hfα : ∀ a, I.ev N (f a) = α a := by
    intro a
    have h1 : (Submodule.Quotient.mk (f a) : D.La ⧸ K) = Submodule.Quotient.mk (b a) :=
      LinearMap.congr_fun hf a
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq K).1 h1)
    rw [← hb a]
    exact (tateIso_ev_eq_iff I hN _ _).2
      ⟨z, by rw [← hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hEF : ∀ a c, (N : ℤ) ∣ D.EF (f a) (f c) - ν * D.EF a c := by
    intro a c
    have h1 := I.isom N hN (f a) (f c)
    rw [hfα, hfα] at h1
    have h2 := he _ _ _ _ (hiso a c) h1
    rw [hξν, ← zpow_mul] at h2
    refine ((I.ζ_prim N hN).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, ← h2, mul_inv_cancel]
  obtain ⟨g, hgf, hgν⟩ := hL f ν hN hνc hEF
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgν
  · rw [LevelTwist.twist_ev, ← hfα a]
    exact LevelTwist.ev_congr I hN (hgf a)

theorem exists_root_ext (B : Type) [Field B] [CharZero B] {A N : ℕ} (hN : 0 < N) (hA : A ∣ N) {ζ : B}
    (hζ : IsPrimitiveRoot ζ A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra B L) (ξ : Lˣ), FiniteDimensional B L ∧ IsPrimitiveRoot ξ N ∧
      (ξ : L) ^ (N / A) = algebraMap B L ζ := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have hA0 : 0 < A := Nat.pos_of_dvd_of_pos hA hN
  have : NeZero A := ⟨hA0.ne'⟩
  have hω := IsCyclotomicExtension.zeta_spec N B (CyclotomicField N B)
  set ω := IsCyclotomicExtension.zeta N B (CyclotomicField N B)
  have hq : 0 < N / A := Nat.div_pos (Nat.le_of_dvd hN hA) hA0
  have hω' : IsPrimitiveRoot (ω ^ (N / A)) A := by
    have := hω.pow_of_dvd hq.ne' (Nat.div_dvd_of_dvd hA)
    rwa [Nat.div_div_self hA hN.ne'] at this
  have hη : IsPrimitiveRoot (algebraMap B (CyclotomicField N B) ζ) A :=
    hζ.map_of_injective (algebraMap B (CyclotomicField N B)).injective
  obtain ⟨i, hiA, hi⟩ := hω'.eq_pow_of_pow_eq_one hη.pow_eq_one
  have hic : i.Coprime A := (hω'.pow_iff_coprime hA0 i).1 (by rw [hi]; exact hη)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hA (ZMod.unitOfCoprime i hic)
  have hji : (v : ZMod N).val % A = i % A := by
    have h1 := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at h1
    rw [← ZMod.natCast_val] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  have hξ : IsPrimitiveRoot (ω ^ (v : ZMod N).val) N := hω.pow_of_coprime _ (ZMod.val_coe_unit_coprime v)
  refine ⟨CyclotomicField N B, inferInstance, inferInstance, (hξ.isUnit hN.ne').unit, ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional {N} B (CyclotomicField N B)
  · exact IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hξ)
  · rw [IsUnit.unit_spec, ← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod _ hω'.pow_eq_one, hji,
      Nat.mod_eq_of_lt hiA, hi]

end GlobalTheory.LevCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetExtend

theorem exists_oAct_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) : ∃ a' : OAct O ((Over.pullback f).obj G), ∀ c, a'.act c = (Over.pullback f).map (a.act c) :=
  ⟨{ act := fun c => (Over.pullback f).map (a.act c)
     hom := fun c => by have := a.hom c; infer_instance
     one := by rw [a.one, CategoryTheory.Functor.map_id]
     mul := fun x y => by rw [a.mul, CategoryTheory.Functor.map_comp]
     add := fun x y => by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _ }, fun _ => rfl⟩

theorem lieMult_fibre {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) {G : Over S} [GrpObj G] {O : Type}
    [CommRing O] (a : OAct O G) (a' : OAct O ((Over.pullback x).obj G))
    (h : ∀ c, a'.act c = (Over.pullback x).map (a.act c)) {k' : Type} [Field k'] (y : Sp k' ⟶ Sp k)
    (τ : O →+* k') (n : ℕ) : LieMult a' y τ n ↔ LieMult a (y ≫ x) τ n :=
  LiePull.lieMult_pull O _ _ G _ x _ a a' (isGrpPullback_pullback G x)
    (fun c => by rw [h]; exact pullback.lift_fst _ _ _) k' y τ n


open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap eigLat IsUnivChart) in
theorem lieMult_iff_finrank {k : Type} [Field k] {O : Type} [CommRing O] {G : Over (Sp k)} [GrpObj G]
    (act : OAct O G) [∀ a, IsMonHom (act.act a)] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (τ : O →+* k) (N : ℕ) :
    LieMult act (𝟙 (Sp k)) τ N ↔ Module.finrank k (eigLat hx act.act (fun a => τ a)) = N := by
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  let P : (epsR k ⟶ G) → Prop := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w
  have hP : ∀ w, IsLieEigen act (𝟙 _) τ w ↔ P (e w) := fun w =>
    and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl)
  have key : LieMult act (𝟙 (Sp k)) τ N ↔ ∃ v : Fin N → (epsR k ⟶ G), (∀ i, P (v i)) ∧
      ∀ w, P w → ∃! c : Fin N → k, IsLieComb c v w :=
    ⟨LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ) (Q := P)
      (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left) hP
      (fun c u v => by rw [he, he]; rfl) N,
    LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ) (P := P)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
      (fun w => by rw [hP, e.apply_symm_apply]) (fun c u v => by rw [he', he']; rfl) N⟩
  have mem : ∀ c, c ∈ eigLat hx act.act (fun a => τ a) ↔ P (tvec (x := x) c) := fun c => by
    rw [Chart.mem_eigLat_iff]
    exact ⟨fun h => ⟨(Chart.isTan_iff _).1 (Chart.isTan_tvec hx c), fun a => (Chart.tvec_eig_iff hx _ _ _).2 (h a)⟩,
      fun h a => (Chart.tvec_eig_iff hx _ _ _).1 (h.2 a)⟩
  have ex : ∀ w, P w → ∃ c : eigLat hx act.act (fun a => τ a), w = tvec (x := x) c := fun w hw => by
    have h : w = tvec (x := x) _ := Chart.tcoord_spec hx w ((Chart.isTan_iff _).2 hw.1)
    exact ⟨⟨_, (mem _).2 (h ▸ hw)⟩, h⟩
  have comb : ∀ (b : Fin N → eigLat hx act.act (fun a => τ a)) (c : eigLat hx act.act (fun a => τ a))
      (d : Fin N → k), IsLieComb d (fun i => tvec (x := x) (b i)) (tvec (x := x) c) ↔
        Fintype.linearCombination k b d = c := fun b c d => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    obtain ⟨h, E⟩ := Chart.prodPts_tan hx d (fun i => tvec (x := x) (b i)) fun i => Chart.isTan_tvec hx _
    have E' : prodPts d (fun i => tvec (x := x) (b i)) = tvec (x := x) _ := Chart.tcoord_spec hx _ h
    rw [E', E, Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [Chart.tcoord_tvec, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact ⟨fun h => (Chart.tvec_inj hx h).symm, fun h => by rw [h]⟩
  rw [key]
  constructor
  · rintro ⟨v, hv, H⟩
    choose b hb using fun i => ex _ (hv i)
    obtain rfl : v = fun i => tvec (x := x) (b i) := funext hb
    rw [← (LinearEquiv.ofBijective (Fintype.linearCombination k b) ((Function.bijective_iff_existsUnique _).2
      fun c => (existsUnique_congr (comb b c)).1 (H _ ((mem _).1 c.2)))).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq _ _ h
    refine ⟨fun i => tvec (x := x) (b i), fun i => (mem _).1 (b i).2, fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := ex w hw
    refine (existsUnique_congr (comb b c)).2 ((Function.bijective_iff_existsUnique _).1 ?_ _)
    convert b.equivFun.symm.bijective using 1
    ext r
    simp [Fintype.linearCombination_apply]


open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat fB pushR dualMapA) in
theorem lieMult_extend {S : Scheme.{0}} {G : Over S} [GrpObj G] [Smooth G.hom] {K Ω : Type} [Field K] [Field Ω]
    (i : K →+* Ω) (x : Sp K ⟶ S) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* K) (N : ℕ) :
    LieMult act (spMap i ≫ x) (i.comp τ) N ↔ LieMult act x τ N := by
  let _ := i.toAlgebra
  obtain ⟨a₁, h₁⟩ := exists_oAct_pullback x act
  have E₁ := lieMult_fibre x act a₁ h₁ (𝟙 _) τ N
  rw [Category.id_comp] at E₁
  rw [← E₁, ← lieMult_fibre x act a₁ h₁]
  have : Smooth ((Over.pullback x).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom x))
  generalize_proofs at *
  set G₁ := (Over.pullback x).obj G
  obtain ⟨a₂, h₂⟩ := exists_oAct_pullback (fB K Ω) a₁
  have E₂ := lieMult_fibre (fB K Ω) a₁ a₂ h₂ (𝟙 _) (i.comp τ) N
  rw [Category.id_comp] at E₂
  refine E₂.symm.trans ?_
  have := a₁.hom
  have := a₂.hom
  obtain ⟨n, y, hy⟩ := Chart.univChartLoc G₁
  obtain ⟨y', hy', hc⟩ := Chart.tanBC_alg (R' := Ω) G₁ n y hy
  have hpt : ∀ c : Fin n → K, pushR G₁ (tvec (x := y') (algebraMap K Ω ∘ c)) =
      Chart.spMap (dualMapA K Ω) ≫ tvec (x := y) c := fun c =>
    Over.OverMorphism.ext (by rw [Chart.pushR_left, hc c]; rfl)
  have hL : ∀ a (c : Fin n → K), tmap hy' (a₂.act a) (algebraMap K Ω ∘ c) =
      algebraMap K Ω ∘ tmap hy (a₁.act a) c := fun a c => by
    apply Chart.tvec_inj hy'
    apply Chart.pushR_inj G₁
    rw [Chart.tvec_tmap hy', h₂, Chart.pushR_map, hpt, hpt, Chart.tvec_tmap hy, Category.assoc]
  have hr : Module.finrank K (eigLat hy a₁.act fun a => τ a) =
      Module.finrank Ω (eigLat hy' a₂.act fun a => i.comp τ a) :=
    Chart.finrank_eig_bc (fun a => tmap hy (a₁.act a)) (fun a => tmap hy' (a₂.act a)) hL τ
  rw [lieMult_iff_finrank a₂ hy', lieMult_iff_finrank a₁ hy, hr]

theorem exists_factor {O K Ω : Type} [CommRing O] [Algebra.IsIntegral ℤ O] [Field K] [IsAlgClosed K] [Field Ω]
    (i : K →+* Ω) (σ : O →+* Ω) : ∃ τ : O →+* K, i.comp τ = σ := by
  let _ := i.toAlgebra
  have h : ∀ a, σ a ∈ i.range := fun a => by
    have h₀ : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
    have h₁ : IsIntegral K (σ a) := h₀.tower_top
    exact minpoly.mem_range_of_degree_eq_one K _
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h₁))
  let e : K ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b hab => i.injective (congrArg Subtype.val hab), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (σ.codRestrict _ h), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (σ.codRestrict _ h a))

end GlobalTheory.DetExtend

theorem GlobalTheory.detCond_iff_of_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) [IsAlgClosed K] [CharZero K] (act : OAct (𝓞 E) G) (ρ : K), Smooth G.hom → (DetCond D act (spMap i ≫ x) (i ρ) ↔ DetCond D act x ρ) := by
  intro E _ _ _ H D S G _ K Ω _ _ i x _ _ act ρ _
  have key : ∀ τ : 𝓞 E →+* K,
      ((i.comp τ H.rt = i ρ → LieMult act (spMap i ≫ x) (i.comp τ) D.p) ∧
        (i.comp τ H.rt ≠ i ρ → LieMult act (spMap i ≫ x) (i.comp τ) D.q)) ↔
      ((τ H.rt = ρ → LieMult act x τ D.p) ∧ (τ H.rt ≠ ρ → LieMult act x τ D.q)) := fun τ => by
    rw [DetExtend.lieMult_extend, DetExtend.lieMult_extend, RingHom.comp_apply, Ne, i.injective.eq_iff]
  refine ⟨fun h τ => (key τ).1 (h _), fun h σ => ?_⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor i σ
  exact (key τ).2 (h τ)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem finrank_int_eq_mul (O M : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := M) le_rfl
  let F : Submodule O M := Submodule.span O (Set.range f)
  let bF : Module.Basis (Fin (Module.finrank O M)) O F := Module.Basis.span hf
  have : Module.Free O F := Module.Free.of_basis bF
  have h1 : Module.finrank O F = Module.finrank O M := by
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin]
  have h2 : Module.finrank O (M ⧸ F) = 0 := by
    have := Submodule.finrank_quotient_add_finrank F
    omega
  have h3 : Module.finrank ℤ (M ⧸ F.restrictScalars ℤ) = 0 := by
    rw [Module.finrank_eq_zero_iff] at h2 ⊢
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha, hax⟩ := h2 (Submodule.Quotient.mk x)
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨r, hr, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax ⊢
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul O r x, hc, mul_comm, mul_smul]
    exact F.smul_mem c hax
  have h4 := Submodule.finrank_quotient_add_finrank (F.restrictScalars ℤ)
  have h5 : Module.finrank ℤ (F.restrictScalars ℤ) = Module.finrank ℤ O * Module.finrank O F :=
    (Module.finrank_mul_finrank ℤ O F).symm
  rw [← h4, h3, zero_add, h5, h1]

theorem finrank_int_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) :
    Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  have := D.fin
  rw [finrank_int_eq_mul (𝓞 E) D.La, D.rank, RingOfIntegers.rank, IsTotallyComplex.finrank E,
    Nat.mul_div_cancel_left _ two_pos, Nat.mul_assoc]

theorem exists_equiv_stdSymp {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hp : Function.Bijective B) {g : ℕ}
    (hg : Module.finrank ℤ M = 2 * g) :
    ∃ bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M,
      ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j := by
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  let e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)
  have hl : ∀ i, ((e (Sum.inl i) : Fin (2 * g)) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e (Sum.inr i) : Fin (2 * g)) : ℕ) = g + i := fun i => by simp [e]; omega
  refine ⟨(b.reindex e).equivFun.symm, fun i j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have hs : ∀ k, (b.reindex e).equivFun.symm (Pi.single (e k) 1) = b k := fun k => by
    rw [Module.Basis.equivFun_symm_apply]; simp [Pi.single_apply]
  rw [hs, hs, Out.stdSymp]
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2
  · rw [hb.left_left, hl, hl, if_neg (by omega), if_neg (by omega)]
  · rw [hb.left_right, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_left hB, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_right, hr, hr, if_neg (by omega), if_neg (by omega)]

theorem exists_isSympBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    ∃ bas : (Fin (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → ℤ) ≃ₗ[ℤ] D.La, IsSympBasis D bas := by
  intro E _ _ _ H D
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := inferInstance
  exact exists_equiv_stdSymp D.alt D.unimod (finrank_int_lattice D)

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocally
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocally
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.LocalCoord

theorem appLE_resG {X Y : Scheme.{0}} (x : Y ⟶ X) {U U' : X.Opens} (hU : U' ≤ U) {V : Y.Opens} (h : V ≤ x ⁻¹ᵁ U')
    (a : Γ(X, U)) : (x.appLE U' V h).hom (resG X hU a) = (x.appLE U V (h.trans (x.preimage_mono hU))).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem resG_appLE {X Y : Scheme.{0}} (x : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(X, U)) : resG Y hV ((x.appLE U V h).hom a) = (x.appLE U V' (hV.trans h)).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem res_val_lemma {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := by
  rfl

private theorem res_pullU_val_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)ˣ) : ((res h (pullU f W u) : Γ(Y, V)ˣ) : Γ(Y, V)) = (f.appLE W V h).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_U_le_preimage_U {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) (k : PUnit) :
    (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j k) := by
  intro y hy
  have hy' : y ∈ ⋂ k, f ⁻¹' (M.U (j k) : Set X) := hy
  exact Set.mem_iInter.1 hy' k

private theorem resG_app_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)) : resG Y h ((f.app W).hom u) = (f.appLE W V h).hom u := by
  rfl

private theorem pullU_val_eq_app {X Y : Scheme.{0}} (f : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    ((pullU f W u : Γ(Y, f ⁻¹ᵁ W)ˣ) : Γ(Y, f ⁻¹ᵁ W)) = (f.app W).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_g_lemma_6 {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull f).g j j' : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ) : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')) =
      (f.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp only [Fintype.prod_unique, zpow_one]
  rfl

private theorem resG_eq_presheaf_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG X h a = (X.presheaf.map (homOfLE h).op).hom a := by
  rfl

theorem exists_secCoord_of_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) {I : Type} (th : I → M.Sec)
    {R : Type} [CommRing R] (x : Sp R ⟶ X) (j₀ : M.ι) (h₀ : ⊤ ≤ x ⁻¹ᵁ M.U j₀) : ∃ v, SecCoord M th x v := by
  have hV : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U j₀) := by
    intro j y hy
    exact ⟨pull_U_le_preimage_U M x j PUnit.unit hy, h₀ trivial⟩
  let τ : (M.pull x).Gen := ⟨fun j => res (hV j) (pullU x _ (M.g (j PUnit.unit) j₀))⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE (M.U j₀) ⊤ h₀).hom ((th i).f j₀)), τ, ?_, ?_⟩
  · intro j j'
    apply Units.ext
    have hc := congrArg Units.val (hM.cocycle (j PUnit.unit) (j' PUnit.unit) j₀)
    simp only [Units.val_mul, res_val_lemma] at hc
    have hT : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) ⊓ M.U j₀) := by
      intro y hy
      exact ⟨⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩, h₀ trivial⟩
    have hc' := congrArg (x.appLE _ _ hT).hom hc
    rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at hc'
    have hjj : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) := by
      intro y hy
      exact ⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩
    simp only [τ, Units.val_mul, res_val_lemma, pullU_val_eq_app, resG_app_eq_appLE, resG_appLE, pull_g_lemma_6 M x j j' hjj]
    exact hc'.symm
  · intro i j h
    have hf := (th i).compat (j PUnit.unit) j₀
    simp only [τ, res_pullU_val_eq_appLE]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply, resG_appLE,
      ← appLE_resG x (inf_le_left : M.U (j PUnit.unit) ⊓ M.U j₀ ≤ _) (hV j), resG_eq_presheaf_map, hf, map_mul,
      ← resG_eq_presheaf_map, appLE_resG, mul_comm]

theorem exists_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) (p : X) : ∃ j, p ∈ M.U j := by
  have hp : p ∈ (⨆ i, M.U i) := by
    rw [hM.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hp

theorem secCoord_local : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  intro X M I th hM
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _ x
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x (IsLocalRing.closedPoint R))
    refine exists_secCoord_of_chart M hM th x j₀ ?_
    intro y _
    exact (IsLocalRing.specializes_closedPoint (R := R) y).mem_open (x ⁻¹ᵁ M.U j₀).isOpen hj
  · intro R _ x p
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x p)
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := (p : PrimeSpectrum R)) hj
        (x ⁻¹ᵁ M.U j₀).isOpen
    refine ⟨f, hpf, exists_secCoord_of_chart M hM th _ j₀ ?_⟩
    intro y _
    have hy : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (show PrimeSpectrum (Localization.Away f) from y) ∈
        ((PrimeSpectrum.basicOpen (f : R) : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) (f : R)]
      exact ⟨_, rfl⟩
    exact hsub hy
  · intro p
    obtain ⟨j₀, hj⟩ := exists_chart M hM p
    obtain ⟨V, hV, hpV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hj
    have hV' : IsAffineOpen V := hV
    obtain ⟨v, hv⟩ := exists_secCoord_of_chart M hM th (R := Γ(X, V)) hV'.fromSpec j₀ (by
      intro y _
      apply hVU
      have h1 : hV'.fromSpec y ∈ Set.range hV'.fromSpec := ⟨y, rfl⟩
      rw [hV'.range_fromSpec] at h1
      exact h1)
    refine ⟨Γ(X, V), inferInstance, hV'.fromSpec, v, inferInstance, ?_, hv⟩
    rw [hV'.range_fromSpec]
    exact hpV

end GlobalTheory.ZM.LocalCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionCoordinateVector_exists_locally : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.LocalCoord.secCoord_local | exact GlobalTheory.ZM.LocalCoord.secCoord_local | (intros; apply GlobalTheory.ZM.LocalCoord.secCoord_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem existsUnique_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    (hf : ∀ i j (T : Scheme.{0}) (x : T ⟶ Z i) (y : T ⟶ Z j), x ≫ ψ i = y ≫ ψ j → x ≫ f i = y ≫ f j) :
    ∃! F : X ⟶ Y, ∀ i, ψ i ≫ F = f i := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers I Z ψ (fun x => by simpa using hc x) hψ
  refine ⟨C.glueMorphisms f fun i j => hf i j _ _ _ pullback.condition, fun i => C.ι_glueMorphisms _ _ i,
    fun F hF => C.hom_ext _ _ fun i => (hF i).trans (C.ι_glueMorphisms f _ i).symm⟩

theorem hom_ext {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) {F F' : X ⟶ Y}
    (h : ∀ i, ψ i ≫ F = ψ i ≫ F') : F = F' :=
  (existsUnique_hom ψ hψ hc (fun i => ψ i ≫ F') fun _ _ _ _ _ e => by
    rw [← Category.assoc, e, Category.assoc]).unique h fun _ => rfl

theorem exists_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ Z i} {b : ∀ i j, B i j ⟶ Z j}
    (hB : ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) (hf : ∀ i j, a i j ≫ f i = b i j ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, ψ i ≫ F = f i :=
  (existsUnique_hom ψ hψ hc f fun i j _ x y e => by
    rw [← (hB i j).lift_fst x y e, Category.assoc, hf, ← Category.assoc, (hB i j).lift_snd]).exists

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem exists_mem (hU : iSup U = ⊤) (s : S) : ∃ i, s ∈ U i :=
  TopologicalSpace.Opens.mem_iSup.1 (show s ∈ iSup U by rw [hU]; trivial)

theorem isOpenImmersion {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) : IsOpenImmersion ψ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

theorem mem_range {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) (x : X) : x ∈ Set.range ψ ↔ p x ∈ V := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact (q z).2
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h x ⟨p x, hx⟩ rfl
    exact ⟨z, hz⟩

theorem covers (hU : iSup U = ⊤) {X : Scheme.{0}} {Z : I → Scheme.{0}} {p : X ⟶ S} {q : ∀ i, Z i ⟶ (U i).toScheme}
    {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι) (x : X) : ∃ i, x ∈ Set.range (ψ i) :=
  (exists_mem hU (p x)).imp fun i hi => (mem_range (h i) x).2 hi

theorem over_ext (hU : iSup U = ⊤) {T A : Over S} {f g : T ⟶ A}
    (h : ∀ i (T' : Over (U i).toScheme) (r : Over.mk (T'.hom ≫ (U i).ι) ⟶ T), r ≫ f = r ≫ g) : f = g := by
  ext1
  refine hom_ext (fun i => (T.hom ⁻¹ᵁ U i).ι) (fun _ => inferInstance)
    (covers hU fun i => (isPullback_morphismRestrict T.hom (U i)).flip) fun i => ?_
  exact congrArg (fun z => z.left) (h i (Over.mk (T.hom ∣_ U i))
    (Over.homMk (T.hom ⁻¹ᵁ U i).ι (morphismRestrict_ι _ _).symm))

theorem exists_lift {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} (x₀ : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ G, x₀.left = x.left ≫ ψ :=
  ⟨Over.homMk (h.lift x₀.left T.hom (Over.w x₀)) (h.lift_snd _ _ _), (h.lift_fst _ _ _).symm⟩

theorem lift_ext {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} {x y : T ⟶ G} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

end GlobalTheory.CoverGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem good_pullback : Out.GtBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (_ : SABMap t' t f), Good t → Good t' := by
  intro hB E _ _ _ H X X' t t' f m hg
  obtain ⟨hA, hS, hT⟩ := hg
  obtain ⟨cm, cart, base, act, lin⟩ := m
  have hpb := GlobalTheory.AbLocusPull.abLocus_sections_pull X X' f t.G t'.G cm.F t.semi cart
  refine ⟨hpb.1 hA, GlobalTheory.splitFibres_of_isGrpPullback hB X X' f t.G t'.G cm.F cart hS,
    hpb.2 t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ?_ hT⟩
  obtain ⟨w, hw, -⟩ := lin
  exact ⟨w, hw⟩

end GlobalTheory.Models
end

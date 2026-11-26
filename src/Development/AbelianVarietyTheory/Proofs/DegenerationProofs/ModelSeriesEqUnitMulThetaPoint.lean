module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelTheta

theorem series_eq_unit_mul_theta : Laws → TXSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (m : ℕ), Odd m → ∀ (p : D.La → QkPt M.P.D.toPre C (m ^ 2)) (q : D.La → N'.QT (m ^ 2)) (v : D.La → C), (∀ x (z : TFK (R := M.W) C ⟶ M.P.A.A), z.left = (o.I.ev (m ^ 2) x).left ≫ M.φ → M.P.ToA C (m ^ 2) (p x) z) → (∀ x, ν'.QPt (p x) (q x)) → o.Theta m v → (∃ c : Cˣ, ∀ x, N'.tx m (q x) = c * v x) ∧ (3 ≤ m → v ≠ 0) := by
  intro hL hTX E _ _ _ H D C _ _ _ _ _ o M N' ν' m hm p q v hpz hq hv
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun i =>
    Over.homMk ((o.I.ev (m ^ 2) i).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      simp)
  have key := hTX M.W (IsLocalRing.maximalIdeal M.W) M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm
    D.La p q x (fun i => hpz i (x i) rfl) hq
  have hm0 : (m : C) ≠ 0 := Nat.cast_ne_zero.mpr hm.pos.ne'
  have hmu : IsUnit ((m : ℕ) : Γ(Sp C, ⊤)) := by
    have h1 : ((m : ℕ) : Γ(Sp C, ⊤)) = fnOf (m : C) := (map_natCast _ m).symm
    rw [h1]
    exact (IsUnit.mk0 _ hm0).map _
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have htors : ∀ i, o.I.ev (m ^ 2) i ^ (m ^ 2) = 1 := fun i => (o.I.onto (m ^ 2) hm2 _).2 ⟨i, rfl⟩
  have : Subsingleton (TFK (R := M.W) C).left := by
    change Subsingleton (PrimeSpectrum C)
    exact ⟨fun a b => PrimeSpectrum.ext (by
      have := a.isPrime
      have := b.isPrime
      rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])⟩
  have : Nonempty (TFK (R := M.W) C).left := by
    change Nonempty (PrimeSpectrum C)
    exact ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  have c1 := (GlobalTheory.CoordSep.isThetaPt_iff (T := TFK (R := M.W) C) hm hmu x _).1 key
  have hτ : 𝟙 (Sp C) ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := by simp
  have hβ : 𝟙 (Sp C) ≫ Over.Hom.left (𝟙 (TFK (R := M.W) C)) = 𝟙 (Sp C) := by simp
  have hx : ∀ i, 𝟙 (Sp C) ≫ (x i).left = (o.I.ev (m ^ 2) i).left ≫ M.φ := fun i => Category.id_comp _
  have hz := GlobalTheory.ThetaPtMove.over_one (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) M.cart (𝟙 (Sp C)) hτ
  have hg : ∀ th₀, IsGenSec M.P.A.A M.P.A.L 1 th₀ →
      IsGenSec M.P.A.A M.P.A.L 1 (VVRank.pullS M.P.A.A 1 (𝟙 (TFK (R := M.W) C)) th₀) :=
    fun th h => GlobalTheory.ThetaCoord.isGenSec_pullS M.P.A.isLB (𝟙 _) (𝟙 _) (by simp) h
  have hσ : IsIso (𝟙 (Sp C) : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left) := IsIso.id (Sp C)
  have c2 := GlobalTheory.FullExtend.isCoordPt_move (S := Sp (FractionRing M.W)) (S' := Sp C) (f := jFK (R := M.W) C)
    (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) (𝟙 (Sp C)) (P₀ := M.P.A) (P := o.P) (φ := M.φ) M.cart M.lb
    (B := TFK (R := M.W) C) (𝟙 (Sp C)) (𝟙 _) hβ hτ hg (k := m) (I := D.La) (x := o.I.ev (m ^ 2)) (x₀ := x) hx htors
    (z := 1) (z₀ := 1) hz (v₀ := fun i => fnOf (N'.tx m (q i))) c1
  have e1 : ∀ y : Γ(Sp C, ⊤), (𝟙 (Sp C) : Sp C ⟶ Sp C).appTop.hom y = y := fun y => by simp
  simp only [e1] at c2
  obtain ⟨-, huniq, hthc, hsep⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate hL C (Sp C) o.P (𝟙 (Sp C)) m hm hm0
    D.La (o.I.ev (m ^ 2)) htors
  have hv1 : IsCoordPt o.P m (o.I.ev (m ^ 2)) 1 (fun i => fnOf (v i)) := (hthc v).1 hv
  obtain ⟨c, hc⟩ := (huniq 1 v (fun i => N'.tx m (q i)) hv1).1 c2
  refine ⟨⟨c, fun i => ?_⟩, fun h3 => ?_⟩
  · have := congrFun hc i
    simpa using this
  · have hall : ∀ y : Over.mk (𝟙 (Sp C)) ⟶ o.P.A, y ^ m ^ 2 = 1 → ∃ i, o.I.ev (m ^ 2) i = y :=
      fun y hy => (o.I.onto (m ^ 2) hm2 y).1 hy
    exact (hsep h3 hall 1 1 v hv1 hv1).2

end GlobalTheory.ModelTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelSeries_eq_unit_mul_thetaPoint : Laws → TXSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (m : ℕ), Odd m → ∀ (p : D.La → QkPt M.P.D.toPre C (m ^ 2)) (q : D.La → N'.QT (m ^ 2)) (v : D.La → C), (∀ x (z : TFK (R := M.W) C ⟶ M.P.A.A), z.left = (o.I.ev (m ^ 2) x).left ≫ M.φ → M.P.ToA C (m ^ 2) (p x) z) → (∀ x, ν'.QPt (p x) (q x)) → o.Theta m v → (∃ c : Cˣ, ∀ x, N'.tx m (q x) = c * v x) ∧ (3 ≤ m → v ≠ 0) := by
  first | exact @GlobalTheory.ModelTheta.series_eq_unit_mul_theta | exact GlobalTheory.ModelTheta.series_eq_unit_mul_theta | (intros; apply GlobalTheory.ModelTheta.series_eq_unit_mul_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsMatchOfLevelGeFour
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsMatchOfLevelGeFour
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait.LevelFour

theorem exists_image {C : Type} [Field C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, J.Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, hg⟩
  have a := hp k
  rw [N.mem_QT.1 p.2] at a
  exact (h₁ _).unique a (h₃ _)

theorem ev_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2)
    {g : N.Gt} {g' : N'.Gt} (hg : J.Rel g g') :
    N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun χ => (H χ).2 g g' hg

theorem labels_of_four_le : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  intro hL hE hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT hR n hn h3 hl k hk
    x p q' p' z hp e₁ e₂ hq hz
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  choose pt hpt using fun i : D.La => (existsUnique_twRel A.be u (r (n ^ 2)) (hr.pow hn2) (A.q (n ^ 2) i)).exists
  choose qt hq₁ hq₂ using fun i => exists_image J (pt i)
  choose pp hpp using fun i => (B.2.2.2.2 (n ^ 2)).2.1 (qt i)
  have hA : ∀ i, M.P.ToA C (n ^ 2) (pp i) (e (o.I.ev (n ^ 2) i)) := fun i =>
    hl i (pt i) (qt i) (pp i) _ (hpt i) (hq₁ i) (hq₂ i) (hpp i) (he _)
  obtain ⟨F, hF, -⟩ := hT C k (by omega)
  obtain ⟨y, hy⟩ := e.surjective (F p')
  have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' n hn D.La pp qt _ hA hpp
    k hk p' q' (F p') ((hF _ _).2 rfl) hq
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have ht : ∀ i, o.I.ev (n ^ 2) i ^ (n ^ 2) = 1 := fun i => (o.I.onto _ hn2 _).2 ⟨i, rfl⟩
  have Q₁ : IsCoordPt o.P n (T := baseOver (Sp C)) (o.I.ev (n ^ 2)) y fun i => fnOf (N'.ev n (qt i) q'.1.2) :=
    FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (he _)) ht (z := y)
      ((Category.id_comp _).trans ((congrArg (fun w => w.left) hy).symm.trans (he _))) Q
  have Q₂ := ((hR.2.2.2 n hn pt hpt).2.2 k (by omega) x p hp).2
  obtain ⟨-, s₂, -, s₄⟩ := CoordSep.coord_exists_unique_separate hL.1 C (Sp C) o.P (𝟙 _) n hn
    (Nat.cast_ne_zero.2 hn.pos.ne') D.La (o.I.ev (n ^ 2)) ht
  have Q₃ := (s₂ _ _ (fun i => N'.ev n (qt i) q'.1.2) Q₂).2
    ⟨J.lam * J.h p.1.2.b ^ (n ^ 2), funext fun i => ev_iso J hn (hq₁ i) (hq₂ i) e₂⟩
  obtain rfl := (s₄ h3 (fun w hw => (o.I.onto _ hn2 w).1 hw) _ _ _ Q₃ Q₁).1
  exact (hF _ _).2 ((Over.OverMorphism.ext (hz.trans (he _).symm)).trans hy)

end GlobalTheory.Ex.Trait.LevelFour
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsMatchOfLevelGeFourStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedLabels_match_of_level_ge_four : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  first | exact @GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le | exact GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le | (intros; apply GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetBCGen

open TrivSqZeroExt

theorem spMap_comp_gen {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : C →+* A) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem surj_fst (R : Type) [CommRing R] : Function.Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  intro P
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber R)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem isLocalRing_dual (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

theorem map_inl_inr {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (F : DualNumber R →+* DualNumber K)
    (hF1 : ∀ a, F (algebraMap R _ a) = algebraMap K _ (f a)) (hF2 : F DualNumber.eps = DualNumber.eps) (a b : R) :
    F (inl a) = inl (f a) ∧ F (inr b) = inr (f b) := by
  have h1 : ∀ a, F (inl a) = inl (f a) := fun a => by
    have := hF1 a
    rwa [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl] at this
  refine ⟨h1 a, ?_⟩
  have e : ∀ {S : Type} [CommRing S] (c : S), (inr c : DualNumber S) = inl c * DualNumber.eps := fun c => by
    rw [DualNumber.eps, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, _root_.mul_one]
  rw [e, map_mul, h1, hF2, ← e]

theorem valR_spMap_comp' {A A' : Type} [CommRing A] [CommRing A'] {Y : Scheme.{0}} (ψ : A →+* A') (x : Sp A ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by
  have h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V := fun y _ => h (Set.mem_univ ((spMap ψ) y))
  unfold valR
  rw [dite_eq_left h', dite_eq_left h]
  have e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.ThetaPtMove

theorem pow_eq_one_of_gen {K : Type} [Field K] (P : PolAV (Sp K)) (k : ℕ) {T : Over (Sp K)} (x : T ⟶ P.A)
    (α : LB.Gen (thetaLB P.A P.L ((k : ℕ) : ℤ) x)) (hα : α.IsGen) : x ^ k = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact pow_zero x
  refine (GlobalTheory.abelianSchemeLaws_all.1.kerPow (Sp K) P k hk T x).1 fun p => ⟨⊤, trivial, ?_⟩
  exact (GlobalTheory.KerPow.pull_iff _ _ _).2 (GlobalTheory.KerPow.HasGen.pull ⟨α, hα⟩ _ fun _ => rfl)

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC

theorem gs_theta {X X' : Scheme.{0}} {L₀ : LB X} {L₁ : LB X'} {φ : X' ⟶ X} (w : LB.Iso L₁ (L₀.pull φ))
    (θ₀ : L₀.Sec) (θ : L₁.Sec)
    (H : ∀ (j : (L₀.pull φ).ι) (i : L₁.ι) (h : (L₀.pull φ).U j ⊓ L₁.U i ≤ φ ⁻¹ᵁ L₀.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (θ₀.f (j PUnit.unit)) =
        (show Γ(X', (L₀.pull φ).U j ⊓ L₁.U i) from (w.s (j, i)).val) * resG _ inf_le_right (θ.f i))
    (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L₀.ι) (k : L₁.ι) (hj : φ (r z) ∈ L₀.U j) (hk : r z ∈ L₁.U k) :
    gs (r ≫ φ) z _ (θ₀.f j) = (gw w r z j k).val * gs r z _ (θ.f k) := by
  have hV : r z ∈ (L₀.pull φ).U (fun _ => j) ⊓ L₁.U k := ⟨mem_pull.2 hj, hk⟩
  have hle : (L₀.pull φ).U (fun _ => j) ⊓ L₁.U k ≤ φ ⁻¹ᵁ L₀.U j := fun y hy => mem_pull.1 hy.1
  rw [← gs_appLE' φ _ _ hle r z hV, H (fun _ => j) k hle, gs_mul _ _ _ hV]
  congr 1
  · exact gs_unit r z _ hV (w.s (fun _ => j, k))
  · exact gs_res _ _ _ hV _

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.ConstFam GlobalTheory.GlobalLift

theorem one_left_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  show (toUnit T ≫ η[A]).left = _
  rw [Over.comp_left]
  rfl

theorem tr_move_gen {S S' : Scheme.{0}} {P₀ : PolAV S} {P : PolAV S'} {f : S' ⟶ S} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {w : LB.Iso P.L (P₀.L.pull φ)}
    {ρ₀ : LB.Gen (P₀.L.pull (eSec P₀.A))} {ρ : LB.Gen (P.L.pull (eSec P.A))}
    (hw : w.IsGen) (he : eSec P.A ≫ φ = f ≫ eSec P₀.A)
    (hρ : PMaps w (fun _ : PUnit => eSec P.A) (fun _ => eSec P₀.A) (fun _ => 1) ρ ρ₀ f) {m : ℕ}
    {th₀ th t₀ t} (h : SecRel hp τ hτ w th th₀) (ht : SecRel hp τ hτ w t t₀) {U₀ U}
    (hU : ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' →
      IsActOf P₀.A P₀.L ((m ^ 2 : ℕ) : ℤ) U₀ s₀ s₀' → IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s s')
    (H : Tr P₀ ρ₀ m th₀ U₀ t₀) : Tr P ρ m th U t := by
  obtain ⟨α₀, s₀, hα₀, hn, h₁, h₂⟩ := H
  obtain ⟨α, hα, v⟩ := exists_genThrough₂ hp τ hτ hw P₀.isLB P.isLB (psi_pow hp τ hτ m) α₀ hα₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw P₀.isLB P.isLB s₀
  refine ⟨α, s, hα, corr_of_val P.isLB fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ P₀.isLB P.isLB (psi_pow hp τ hτ m) hα v h hs h₁, hU _ _ _ _ hs ht h₂⟩
  obtain ⟨J, hJ⟩ := exists_good' P₀.isLB y
  have q := val_corr hJ hn (𝟙 _ ≫ τ)
  have q₁ := v _ (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) y J J' hJ hJ'
  rw [Category.assoc, psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc] at q₁
  have q₂ := pmaps_val (fun _ => he) hρ (𝟙 _ ≫ T.hom) hJ hJ'
  rw [Fintype.prod_unique] at q₂
  rw [val_pull hJ, val_rigT' _ _ _ _ _ _ _ _ hJ, Category.assoc _ τ T₀.hom, hτ, ← Category.assoc, q₁, q₂] at q
  rw [val_pull hJ', val_rigT' _ _ _ _ _ _ _ _ hJ']
  have e₁ : (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) ≫ (snd T P.A).left = (𝟙 _ ≫ T.hom) ≫ eSec P.A := by
    rw [Category.id_comp, ptSecT_snd, one_left_eq, Category.id_comp]
  have e₂ : (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) ≫ (snd T P.A ^ m).left = (𝟙 _ ≫ T.hom) ≫ eSec P.A := by
    rw [Category.id_comp, ← Over.comp_left, MonObj.comp_pow, ← e₁, Category.id_comp, ← Over.comp_left,
      show ptSecT P.A (1 : T ⟶ P.A) ≫ snd T P.A = 1 from lift_snd _ _, one_pow]
  rw [e₁, e₂] at q
  rw [zpow_one, mul_zpow, ← zpow_add] at q
  have e₃ : ((m ^ 2 : ℕ) : ℤ) + -((1 : ℕ) : ℤ) = ((m ^ 2 : ℕ) : ℤ) - 1 := by push_cast; ring
  rw [e₃] at q
  exact mul_left_cancel q

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open TrivSqZeroExt

theorem one_add_inr_pow {K : Type} [Field K] (e : K) (M : ℕ) :
    ((1 : DualNumber K) + inr e) ^ M = 1 + inr ((M : K) * e) := by
  induction M with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ih]; ext <;> simp <;> ring

theorem dual_solve {K : Type} [Field K] (M : ℕ) (u₁ T' : DualNumber K) (u₀ r a b : K) (hu : u₁.fst = u₀)
    (h0 : u₀ ≠ 0) (h : u₁ ^ M * T' = inl ((u₀ * r) ^ M) * (inl a + inr b)) :
    T' = inl (r ^ M) * (inl a + inr (b - (M : K) * (u₁.snd / u₀) * a)) := by
  have hv : u₁ = inl u₀ * (1 + inr (u₁.snd / u₀)) := by
    ext
    · simp [hu]
    · simp [hu]; field_simp
  rw [hv, mul_pow, one_add_inr_pow, mul_pow, inl_mul, inl_pow, _root_.mul_assoc, _root_.mul_assoc] at h
  have hu0 : IsUnit (inl (u₀ ^ M) : DualNumber K) := by
    refine ⟨⟨inl (u₀ ^ M), inl ((u₀ ^ M)⁻¹), ?_, ?_⟩, rfl⟩ <;>
      rw [← inl_mul] <;> simp [pow_ne_zero M h0]
  have h' := hu0.mul_left_cancel h
  have hinv : (1 - inr ((M : K) * (u₁.snd / u₀)) : DualNumber K) * (1 + inr ((M : K) * (u₁.snd / u₀))) = 1 := by
    ext <;> simp
  calc T' = (1 - inr ((M : K) * (u₁.snd / u₀))) * ((1 + inr ((M : K) * (u₁.snd / u₀))) * T') := by
        rw [← _root_.mul_assoc, hinv, _root_.one_mul]
    _ = _ := by rw [h']; ext <;> simp <;> ring

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ZH.ThetaData

theorem valR_secRel {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
    (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℕ} {t₀ : LB.Sec (LPow G L₀ (k : ℤ) T₀)} {t : LB.Sec (LPow A L₁ (k : ℤ) T)}
    (ht : SecRel hp τ hτ w t t₀) {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ (T ⊗ A).left)
    (j : L₀.ι) (i : L₁.ι) (hj : φ ((y ≫ (snd T A).left) (IsLocalRing.closedPoint C)) ∈ L₀.U j)
    (hi : (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) ∈ L₁.U i) :
    valR (y ≫ psi hp τ hτ) ((LPow G L₀ (k : ℤ) T₀).U fun _ => j) (t₀.f fun _ => j) =
      valR (y ≫ (snd T A).left) _ (w.s (fun _ => j, i)).val ^ k *
        valR y ((LPow A L₁ (k : ℤ) T).U fun _ => i) (t.f fun _ => i) := by
  have e₀ : (y ≫ psi hp τ hτ) ≫ (snd T₀ G).left = (y ≫ (snd T A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd']
  have m₀ : (y ≫ psi hp τ hτ) (IsLocalRing.closedPoint C) ∈ (LPow G L₀ (k : ℤ) T₀).U fun _ => j :=
    Set.mem_iInter.2 fun _ => by
      show ((y ≫ psi hp τ hτ) ≫ (snd T₀ G).left) (IsLocalRing.closedPoint C) ∈ L₀.U j
      rw [e₀]; exact hj
  have m₁ : y (IsLocalRing.closedPoint C) ∈ (LPow A L₁ (k : ℤ) T).U fun _ => i := Set.mem_iInter.2 fun _ => hi
  have mW : (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) ∈ ((L₀.pull φ).div L₁).U (fun _ => j, i) :=
    ⟨mem_pull.2 hj, hi⟩
  obtain ⟨J', hJ', e'⟩ := exists_good L₁ hL₁ (IsLocalRing.closedPoint C) (fun _ : Unit => y ≫ (snd T A).left)
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  obtain ⟨J, hJ, e⟩ := exists_good L₀ hL₀ (IsLocalRing.closedPoint C)
    (fun _ : Unit => (y ≫ (snd T A).left) ≫ φ) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have q := ht _ y (IsLocalRing.closedPoint C) J J' hJ hJ'
  have q₀ := (sval_of (φ := fun _ : Fin 1 => (snd T₀ G).left) (ε := fun _ => (k : ℤ)) t₀ _ _ J (fun _ => j)
      (fun _ => by rw [e₀]; exact e ())).symm.trans (q.trans (congrArg (_ * ·)
    (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => (k : ℤ)) t _ _ J' (fun _ => i)
      (fun _ => e' ()))))
  clear q
  have hw : GlobalTheory.ConstFam.wVal w (IsLocalRing.closedPoint C) J J' (y ≫ (snd T A).left) =
      gw w (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) j i := by
    show gw w (y ≫ (snd T A).left) (IsLocalRing.closedPoint C) (J _) (J' _) = _
    rw [e (), e' ()]
  rw [valR_eq_gs _ _ m₀, valR_eq_gs _ _ m₁, valR_eq_gs _ _ mW, ← map_pow, ← map_mul]
  congr 1
  refine q₀.trans ?_
  rw [hw, gs_unit _ _ _ mW, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

end GlobalTheory.MBLow.JetBCGen

namespace GlobalTheory.MBLow.JetBCGen

open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.ZH.ThetaData

theorem valR_rigRel {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ : LB.Gen (L₁.pull (eSec A))}
    (he : eSec A ≫ φ = f ≫ eSec G)
    (hρ : PMaps w (fun _ : PUnit => eSec A) (fun _ => eSec G) (fun _ => 1) ρ ρ₀ f)
    {C : Type} [CommRing C] [IsLocalRing C] (s : Sp C ⟶ S') (j : L₀.ι) (i : L₁.ι)
    (hj : φ ((s ≫ eSec A) (IsLocalRing.closedPoint C)) ∈ L₀.U j)
    (hi : (s ≫ eSec A) (IsLocalRing.closedPoint C) ∈ L₁.U i) :
    valR (s ≫ f) ((L₀.pull (eSec G)).U fun _ => j) (ρ₀.s fun _ => j).val =
      valR (s ≫ eSec A) _ (w.s (fun _ => j, i)).val * valR s ((L₁.pull (eSec A)).U fun _ => i) (ρ.s fun _ => i).val := by
  have q := hρ _ s (IsLocalRing.closedPoint C) (fun _ => j) (fun _ => i) (fun _ => hj) (fun _ => hi)
  rw [Fintype.prod_unique, zpow_one] at q
  have mW : (s ≫ eSec A) (IsLocalRing.closedPoint C) ∈ ((L₀.pull φ).div L₁).U (fun _ => j, i) :=
    ⟨mem_pull.2 hj, hi⟩
  have m₁ : s (IsLocalRing.closedPoint C) ∈ (L₁.pull (eSec A)).U fun _ => i := mem_pull.2 hi
  have m₀ : (s ≫ f) (IsLocalRing.closedPoint C) ∈ (L₀.pull (eSec G)).U fun _ => j := by
    refine mem_pull.2 ?_
    show ((s ≫ f) ≫ eSec G) (IsLocalRing.closedPoint C) ∈ L₀.U j
    rw [Category.assoc, ← he, ← Category.assoc]
    exact hj
  rw [valR_eq_gs _ _ m₀, valR_eq_gs _ _ mW, valR_eq_gs _ _ m₁, ← map_mul]
  congr 1
  rw [gs_unit _ _ _ m₀, gs_unit _ _ _ mW, gs_unit _ _ _ m₁, ← Units.val_mul]
  exact congrArg Units.val q

end GlobalTheory.MBLow.JetBCGen


open GlobalTheory.MBLow.JetBC GlobalTheory.ThetaPtMove GlobalTheory.MBLow.JetBCGen TrivSqZeroExt in
theorem GlobalTheory.MBLow.thJet_of_keyAtMap : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x' : KeyIn K) (φ : x'.P.A.left ⟶ x.P.A.left), KeyAtMap x' x f φ → ∀ (g : ℕ) (hg : x.P.g = g) (hg' : x'.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (pt' : I → (baseOver (Sp K) ⟶ x'.P.A)) (ϑ : I → R) (J : I → Fin g → R), (∀ i, (pt' i).left ≫ φ = spMap f ≫ (pt i).left) → ThJet x hg m pt ϑ J → ThJet x' hg' m pt' (fun i => f (ϑ i)) (fun i j => f (J i j)) := by
  intro R K _ _ f x x' φ hK g hg hg' m I pt pt' ϑ J hpt ⟨th, hth, H⟩
  obtain ⟨he, w, hgg, F, hp, hw, hrig, hθ, hF1, hF2, hv⟩ := hK
  have := x'.P.isAb.comm
  haveI : IsLocalRing (DualNumber K) := isLocalRing_dual K
  let τ : (baseOver (Sp K)).left ⟶ (baseOver (Sp R)).left := spMap f
  have hτ : τ ≫ (baseOver (Sp R)).hom = (baseOver (Sp K)).hom ≫ spMap f := by simp [τ]
  obtain ⟨U₀, t₀, i₀, c, h₁, h₂, h₃⟩ := H
  obtain ⟨th', hth'⟩ := exists_secRel hp τ hτ hw x.P.isLB x'.P.isLB th
  choose t ht using fun a => exists_secRel hp τ hτ hw x.P.isLB x'.P.isLB (t₀ a)
  have hx : ∀ a, τ ≫ (pt a).left = (pt' a).left ≫ φ := fun a => (hpt a).symm
  have hn : ∀ a, pt' a ^ (m ^ 2) = 1 := fun a => by
    have hx' : τ ≫ (U₀ a).pt.left = (pt' a).left ≫ φ := by rw [(h₁ a).1.pt_eq]; exact hx a
    obtain ⟨α, hα, -⟩ := exists_genThrough₂ hp τ hτ hw x.P.isLB x'.P.isLB (psi_tr' hp τ hτ (pt' a) _ hx')
      (U₀ a).φ (U₀ a).isGen
    exact pow_eq_one_of_gen x'.P (m ^ 2) (pt' a) α hα
  choose U hU hU' using fun a => symLift_move hp τ hτ hw x.P.isLB x'.P.isLB (hx a) (hn a) (h₁ a).1
  have hρ : PMaps w (fun _ : PUnit => eSec x'.P.A) (fun _ => eSec x.P.A) (fun _ => 1) x'.rig x.rig (spMap f) :=
    (maps_iff _ _ _ _ _ _ _ _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hrig
  let o : Sp K := IsLocalRing.closedPoint K
  have ho : ∀ p : Sp K, p = o := fun p => Subsingleton.elim _ _
  obtain ⟨i₁, hi₁⟩ := exists_chart x'.P.isLB (eSec x'.P.A o)
  have hR : ∀ p : Sp R, eSec x.P.A p ∈ x.P.L.U i₀ := fun p => by
    have := h₂ (Set.mem_univ p); simpa using this
  have hj₁ : φ (eSec x'.P.A o) ∈ x.P.L.U i₀ := by
    have : (eSec x'.P.A ≫ φ) o ∈ x.P.L.U i₀ := by rw [he]; simpa using hR (spMap f o)
    simpa using this
  have tanU : ∀ j, ∀ p : Sp (DualNumber K), (x'.v j).left p = eSec x'.P.A o := fun j p => by
    obtain ⟨q, rfl⟩ := surj_fst K p
    have h := x'.basis.1 j
    rw [ho q]
    exact congrArg (fun r => r o) h
  have tanD : ∀ j, ∀ p : Sp (DualNumber R), (x.v j).left p ∈ x.P.L.U i₀ := fun j p => by
    obtain ⟨q, rfl⟩ := surj_fst R p
    have h := x.basis.1 j
    have e : (x.v j).left ((spMap (TrivSqZeroExt.fstHom R R R).toRingHom) q) = eSec x.P.A q :=
      congrArg (fun r => r q) h
    rw [e]; exact hR q
  let W := ((x.P.L.pull φ).div x'.P.L).U (fun _ => i₀, i₁)
  have mW : ∀ p : Sp K, eSec x'.P.A p ∈ W := fun p => by rw [ho p]; exact ⟨mem_pull.2 hj₁, hi₁⟩
  let y' : Fin g → (Sp (DualNumber K) ⟶ (baseOver (Sp K) ⊗ x'.P.A).left) :=
    fun j => epsLift (x'.v (j.cast hg'.symm))
  let u₁ : Fin g → DualNumber K :=
    fun j => valR (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) W (w.s (fun _ => i₀, i₁)).val
  let u₀ : K := valR (𝟙 (Sp K) ≫ eSec x'.P.A) W (w.s (fun _ => i₀, i₁)).val
  let c' : Fin g → K := fun j => f (c j) - ((m ^ 2 : ℕ) : K) * ((u₁ j).snd / u₀)
  refine ⟨th', polAVSectionInverseImage_chartwisePullback hp τ hτ (gs_theta w x.th x'.th hθ) hth' hth, U, t, i₁, c',
    fun a => ⟨hU a, tr_move_gen hp τ hτ hw he hρ hth' (ht a) (hU' a) (h₁ a).2⟩, ?_, fun a j => ?_⟩
  · intro p _
    rw [ho p]
    exact hi₁
  · let j' : Fin x'.P.g := j.cast hg'.symm
    let j₀ : Fin x.P.g := j.cast hg.symm
    have hvj : (x'.v j').left ≫ φ = spMap F ≫ (x.v j₀).left := by
      have e : j'.cast hgg = j₀ := Fin.ext rfl
      have := hv j'
      rw [e] at this
      exact this
    have ys : y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left = (x'.v j').left := by
      show epsLift _ ≫ _ = _
      rw [epsLift, ← Over.comp_left, lift_snd]
    have yf : y' j ≫ (fst (baseOver (Sp K)) x'.P.A).left = spMap (algebraMap K (DualNumber K)) := by
      show epsLift _ ≫ _ = _
      rw [epsLift, ← Over.comp_left, lift_fst]
      rfl
    have ys₀ : epsLift (x.v j₀) ≫ (snd (baseOver (Sp R)) x.P.A).left = (x.v j₀).left := by
      rw [epsLift, ← Over.comp_left, lift_snd]
    have yf₀ : epsLift (x.v j₀) ≫ (fst (baseOver (Sp R)) x.P.A).left = spMap (algebraMap R (DualNumber R)) := by
      rw [epsLift, ← Over.comp_left, lift_fst]
      rfl
    have hy : y' j ≫ psi hp τ hτ = spMap F ≫ epsLift (x.v j₀) := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, psi_fst', ← Category.assoc, yf, Category.assoc, yf₀]
        show spMap _ ≫ spMap f = _
        rw [spMap_comp_gen, spMap_comp_gen]
        congr 1
        exact RingHom.ext fun a => (hF1 a).symm
      · rw [Category.assoc, psi_snd', ← Category.assoc, ys, hvj, Category.assoc, ys₀]
    have hFl : ∀ b, F (inl b) = inl (f b) := fun b => (map_inl_inr f F hF1 hF2 b 0).1
    have hFr : ∀ b, F (inr b) = inr (f b) := fun b => (map_inl_inr f F hF1 hF2 0 b).2
    have q := h₃ a j
    have top₀ : ⊤ ≤ (epsLift (x.v j₀)) ⁻¹ᵁ
        ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R)))).U fun _ => i₀) :=
      fun p _ => Set.mem_iInter.2 fun _ => by
        show (epsLift (x.v j₀) ≫ (snd (baseOver (Sp R)) x.P.A).left) p ∈ x.P.L.U i₀
        rw [ys₀]
        exact tanD j₀ p
    have qF := congrArg F q
    rw [← valR_spMap_comp' F _ _ top₀, ← hy] at qF
    have hiy : (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) (IsLocalRing.closedPoint (DualNumber K)) ∈ x'.P.L.U i₁ := by
      rw [ys]; exact (congrArg (· ∈ x'.P.L.U i₁) (tanU j' _)).mpr hi₁
    have hjy : φ ((y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) (IsLocalRing.closedPoint (DualNumber K))) ∈ x.P.L.U i₀ := by
      rw [ys]; exact (congrArg (fun p => φ p ∈ x.P.L.U i₀) (tanU j' _)).mpr hj₁
    rw [valR_secRel hp τ hτ x.P.isLB x'.P.isLB (ht a) (y' j) i₀ i₁ hjy hiy] at qF
    rw [map_mul, map_add (f := _), hFl, hFl, hFr, map_pow, map_add (f := _), map_mul] at qF

    have topρ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) :=
      fun p _ => mem_pull.2 (hR p)
    have hr := valR_rigRel he hρ (𝟙 (Sp K)) i₀ i₁ hj₁ hi₁
    rw [Category.id_comp, ← Category.comp_id (spMap f), valR_spMap_comp' f _ _ topρ] at hr
    rw [hr] at qF

    have topW : ⊤ ≤ (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) ⁻¹ᵁ W := fun p _ => by
      show (y' j ≫ (snd (baseOver (Sp K)) x'.P.A).left) p ∈ W
      rw [ys]
      exact (congrArg (· ∈ W) (tanU j' _)).mpr (mW o)
    have hu : (u₁ j).fst = u₀ := by
      have e := valR_spMap_comp' (TrivSqZeroExt.fstHom K K K).toRingHom _ W topW (w.s (fun _ => i₀, i₁)).val
      show (TrivSqZeroExt.fstHom K K K).toRingHom (valR (y' j ≫ _) W _) = valR (𝟙 (Sp K) ≫ eSec x'.P.A) W _
      rw [← e, ys, x'.basis.1 j', Category.id_comp]
      rfl
    have h0 : u₀ ≠ 0 := by
      have m₀ : (𝟙 (Sp K) ≫ eSec x'.P.A) (IsLocalRing.closedPoint K) ∈ W := mW o
      have : IsUnit u₀ := by
        show IsUnit (valR _ W _)
        rw [GlobalTheory.ZH.ThetaData.valR_eq_gs _ _ m₀, gs_unit _ _ _ m₀]
        exact (Units.isUnit _).map _
      exact this.ne_zero
    have key := dual_solve (m ^ 2) (u₁ j) _ u₀ _ (f (ϑ a)) (f (J a j) + f (c j) * f (ϑ a)) hu h0 qF
    rw [key]
    congr 3
    simp only [c']
    push_cast
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x' : KeyIn K) (φ : x'.P.A.left ⟶ x.P.A.left), KeyAtMap x' x f φ → ∀ (g : ℕ) (hg : x.P.g = g) (hg' : x'.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (pt' : I → (baseOver (Sp K) ⟶ x'.P.A)) (ϑ : I → R) (J : I → Fin g → R), (∀ i, (pt' i).left ≫ φ = spMap f ≫ (pt i).left) → ThJet x hg m pt ϑ J → ThJet x' hg' m pt' (fun i => f (ϑ i)) (fun i j => f (J i j)) := by
  first | exact @GlobalTheory.MBLow.thJet_of_keyAtMap | exact GlobalTheory.MBLow.thJet_of_keyAtMap | (intros; apply GlobalTheory.MBLow.thJet_of_keyAtMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.TwoData

theorem exists_scalar_matrix : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  intro K _ P th th' v v' hth hth' hv hv'
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.principalPolarisation_exists_unique_section GlobalTheory.abelianSchemeLaws_all.2.secTwist P
  obtain ⟨a, ha, -⟩ := hb th
  obtain ⟨a', ha', -⟩ := hb th'
  choose M hM using fun i => (hv.2 _ (hv'.1 i)).exists
  have hne : ∀ (s : P.L.Sec) (c : K), (∀ s' : Sp K, ∃ z : P.A.left, P.A.hom z = s' ∧ z ∈ Out.nonzeroLocus s) →
      (∀ i, s.f i = Geo.Tor.constFn P.A.hom _ c * b.f i) → c ≠ 0 := by
    rintro s c hs hc rfl
    obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [hc i, Geo.Tor.constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have h0 := hne th a hth ha
  have h0' := hne th' a' hth' ha'
  refine ⟨a' * a⁻¹, M, mul_ne_zero h0' (inv_ne_zero h0), fun i => ?_, hM⟩
  rw [ha' i, ha i, ← _root_.mul_assoc, Geo.Tor.constFn, Geo.Tor.constFn, Geo.Tor.constFn, ← map_mul, ← map_mul, inv_mul_cancel_right₀ h0]

end GlobalTheory.MBLow.TwoData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_matrix_between_keyData : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  first | exact @GlobalTheory.MBLow.TwoData.exists_scalar_matrix | exact GlobalTheory.MBLow.TwoData.exists_scalar_matrix | (intros; apply GlobalTheory.MBLow.TwoData.exists_scalar_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoefficients
namespace GlobalTheory.NonzeroDeterminantIntegrality

open Matrix

theorem exists_det_ne_zero {K I Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (v : I → Λ → K)
    (h : ∀ c : Λ → K, (∀ i, ∑ l, c l * v i l = 0) → c = 0) :
    ∃ f : Λ → I, (Matrix.of fun a l => v (f a) l).det ≠ 0 := by
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hexp : ∀ x : Λ → K, φ x = ∑ l, φ (Pi.single l 1) * x l := by
      intro x
      conv_lhs => rw [pi_eq_sum_univ' x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hc := h (fun l => φ (Pi.single l 1)) (fun i => by
      rw [← hexp]
      exact hle (Submodule.subset_span ⟨i, rfl⟩))
    apply hφ
    refine LinearMap.ext fun x => ?_
    rw [hexp]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := congrFun hc l
    simp only [Pi.zero_apply] at this
    rw [this, zero_mul]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Λ → K) := Module.Basis.mk hli (by rw [hsp, hspan])
  let e : Λ ≃ κ := (Pi.basisFun K Λ).indexEquiv b
  refine ⟨fun l => a (e l), ?_⟩
  have hli' : LinearIndependent K (Matrix.of fun x l => v (a (e x)) l).row :=
    hli.comp e e.injective
  have := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp this).ne_zero

theorem integral_coefficients : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁]
    (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a : W, i₁ a ≠ 0 → IsUnit a) →
    ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W),
    (∀ c : Λ → K₁, (∀ i : I, ∑ l : Λ, c l * i₁ (u i l) = 0) → c = 0) →
    ∀ (w : I → W) (z : Λ → K₀), (∀ i : I, i₀ (w i) = ∑ l : Λ, z l * i₀ (u i l)) →
    ∃ z₀ : Λ → W, (∀ l : Λ, i₀ (z₀ l) = z l) ∧ ∀ i : I, w i = ∑ l : Λ, z₀ l * u i l := by
  intro W _ _ K₀ K₁ _ _ i₀ i₁ hinj hunit I Λ _ u hu w z hz
  classical
  obtain ⟨f, hf⟩ := exists_det_ne_zero (fun i l => i₁ (u i l)) hu
  let M : Matrix Λ Λ W := Matrix.of fun a l => u (f a) l
  have hdet : IsUnit M.det := by
    apply hunit
    rw [RingHom.map_det]
    exact hf
  let z₀ : Λ → W := M⁻¹ *ᵥ (fun a => w (f a))
  have hM : M *ᵥ z₀ = fun a => w (f a) := by
    simp only [z₀]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hdet₀ : IsUnit (i₀.mapMatrix M).det := by
    rw [← RingHom.map_det]
    exact hdet.map i₀
  have key : (fun l => i₀ (z₀ l)) = z := by
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hdet₀)
    funext a
    have h1 := congrArg i₀ (congrFun hM a)
    rw [hz] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1 ⊢
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨z₀, fun l => congrFun key l, fun i => hinj ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← congrFun key l]

end GlobalTheory.NonzeroDeterminantIntegrality
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.MBLow.coords_integral_of_closed_indep :
  ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W), (∀ c : Λ → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0) → ∀ (w : I → W) (z : Λ → K₀), (∀ i, i₀ (w i) = ∑ l, z l * i₀ (u i l)) → ∃ z₀ : Λ → W, (∀ l, i₀ (z₀ l) = z l) ∧ ∀ i, w i = ∑ l, z₀ l * u i l := by
  first
  | exact @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | (apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients ..)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinates_integral_of_linearly_independent_reduction : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W), (∀ c : Λ → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0) → ∀ (w : I → W) (z : Λ → K₀), (∀ i, i₀ (w i) = ∑ l, z l * i₀ (u i l)) → ∃ z₀ : Λ → W, (∀ l, i₀ (z₀ l) = z l) ∧ ∀ i, w i = ∑ l, z₀ l * u i l := by
  first | exact @GlobalTheory.MBLow.coords_integral_of_closed_indep | exact GlobalTheory.MBLow.coords_integral_of_closed_indep | (intros; apply GlobalTheory.MBLow.coords_integral_of_closed_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_keyAtMap_of_isGrpPullback : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (y : KeyIn R)
    (P : PolAV (Sp K)) (φ : P.A.left ⟶ y.P.A.left) (hp : 1 ≤ P.g) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (hr : rig.IsGen), P.g = y.P.g → IsGrpPullback P.A y.P.A (spMap f) φ → LBIso P.L (y.P.L.pull φ) →
    ∃ th hth v hv, KeyAtMap ⟨P, hp, rig, hr, th, hth, v, hv⟩ y f φ := by
  intro R K _ _ f y P φ hp rig hr hg h hI
  obtain ⟨w, hw0⟩ := hI
  have hw := (isGen_iff w).1 hw0
  have he : eSec P.A ≫ φ = spMap f ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  have := P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale y.P.isLB P.isLB hw (p := P.A.hom) (Over.w η[P.A]) he hr y.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down g' y.P.isLB P.isLB y.th
  have := P.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R K f y.P.A P.A φ h y.P.isAb.smooth y.P.g y.v y.basis
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact hb'
  refine ⟨th', SectionBaseChange.fibre_nonzero_of_pull P.isLB hth' h.1 y.th_ne, _, hb hg, he, w', hg,
    Chart.dualMapR f, h, (isGen_iff _).2 g',
    (maps_iff w' _ (fun _ => eSec y.P.A) _ rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2 m',
    KeyPow.appLE_eq_of_stalk _ y.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (y : KeyIn R) (P : PolAV (Sp K)) (φ : P.A.left ⟶ y.P.A.left) (hp : 1 ≤ P.g) (rig : LB.Gen (P.L.pull (eSec P.A))) (hr : rig.IsGen), P.g = y.P.g → IsGrpPullback P.A y.P.A (spMap f) φ → LBIso P.L (y.P.L.pull φ) → ∃ th hth v hv, KeyAtMap ⟨P, hp, rig, hr, th, hth, v, hv⟩ y f φ := by
  first | exact @GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback | exact GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback | (intros; apply GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_keyIn_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W]
    (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  intro W _ _ _ _ P hg
  have hL := GlobalTheory.abelianSchemeLaws_all
  let m : PrimeSpectrum W := IsLocalRing.closedPoint W
  obtain ⟨th, a, ha, -, hth⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL.1 hL.2 W P m m
  have c : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨b, hb, -, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes W P.A P.g P.smoothDim m m
  have hbu : IsUnit b := (IsLocalRing.mem_maximalIdeal b).not.mp hb |> not_not.mp
  let g : Localization.Away b →+* W := IsLocalization.Away.lift (g := RingHom.id W) b hbu
  have hgf : g.comp (algebraMap W (Localization.Away b)) = RingHom.id W := by
    ext x; simp [g]
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap W (Localization.Away b)))
  have hA₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap W (Localization.Away b))) P.A P.isAb
  have c₁ := hA₁.comm
  have e : spMap g ≫ spMap (algebraMap W (Localization.Away b)) = 𝟙 (Sp W) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgf, CommRingCat.ofHom_id, Spec.map_id]
  have w₁ : 𝟙 P.A.left ≫ P.A.hom = (P.A.hom ≫ spMap g) ≫ spMap (algebraMap W (Localization.Away b)) := by
    rw [Category.assoc, e]; simp
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
  have hid : IsGrpPullback P.A P.A (𝟙 _) (𝟙 P.A.left) := isGrpPullback_of_iso (Iso.refl P.A)
  have h₂ : IsGrpPullback P.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (hid.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ W g _ P.A _ h₂ hA₁.smooth P.g v hv
  obtain ⟨rig, hr⟩ := P.rigid
  refine ⟨⟨P, hg, rig, hr, th, fun s => hth s fun h => ?_, v', hb'⟩, rfl⟩
  have hs : s.asIdeal ≤ IsLocalRing.maximalIdeal W := IsLocalRing.le_maximalIdeal s.isPrime.ne_top
  exact ha (hs h)

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_polarisedAbelian_localDomain : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  first | exact @GlobalTheory.MBLow.exists_keyIn_local | exact GlobalTheory.MBLow.exists_keyIn_local | (intros; apply GlobalTheory.MBLow.exists_keyIn_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem frame_coords_lift {W K₀ K₁ : Type} [CommRing W] [IsDomain W] [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁)
    (hi₀ : Function.Injective i₀) (hi₁ : ∀ a, i₁ a ≠ 0 → IsUnit a) {I : Type} {g : ℕ} (ϑ ϑ' : I → W)
    (J J' : I → Fin g → W)
    (hind : ∀ (c₀ : K₁) (c : Fin g → K₁), (∀ i, c₀ * i₁ (ϑ' i) + ∑ j, c j * i₁ (J' i j) = 0) → c₀ = 0 ∧ c = 0)
    (a₀ : K₀) (M₀ : Matrix (Fin g) (Fin g) K₀) (c₀ : Fin g → K₀)
    (h0ϑ : ∀ i, i₀ (ϑ i) = a₀ * i₀ (ϑ' i))
    (h0J : ∀ i j, i₀ (J i j) = a₀ * ∑ l, M₀ j l * i₀ (J' i l) + c₀ j * i₀ (ϑ' i))
    (a₁ : K₁) (M₁ : Matrix (Fin g) (Fin g) K₁) (c₁ : Fin g → K₁) (ha₁ : a₁ ≠ 0)
    (h1ϑ : ∀ i, i₁ (ϑ i) = a₁ * i₁ (ϑ' i))
    (h1J : ∀ i j, i₁ (J i j) = a₁ * ∑ l, M₁ j l * i₁ (J' i l) + c₁ j * i₁ (ϑ' i)) :
    ∃ (a : W) (M : Matrix (Fin g) (Fin g) W), i₀ a = a₀ ∧ i₁ a = a₁ ∧ i₀.mapMatrix M = M₀ ∧
      i₁.mapMatrix M = M₁ := by
  let u : I → Option (Fin g) → W := fun i o => Option.elim o (ϑ' i) (J' i)
  have hind' : ∀ c : Option (Fin g) → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0 := by
    intro c hc
    obtain ⟨h1, h2⟩ := hind (c none) (fun j => c (some j)) (fun i => by simpa [Fintype.sum_option, u] using hc i)
    funext o
    cases o with
    | none => exact h1
    | some j => exact congrFun h2 j
  obtain ⟨z, hz, hϑz⟩ := GlobalTheory.T.coordinates_integral_of_linearly_independent_reduction W K₀ K₁ i₀ i₁ hi₀ hi₁ I (Option (Fin g)) u hind' ϑ
    (fun o => Option.elim o a₀ 0) (fun i => by simp [Fintype.sum_option, u, h0ϑ])
  have hz0 : ∀ j, z (some j) = 0 := fun j => hi₀ (by simpa using hz (some j))
  have ha₀ : i₀ (z none) = a₀ := by simpa using hz none
  have ha : i₁ (z none) = a₁ := by
    have := hind (i₁ (z none) - a₁) 0 (fun i => by
      have e := congrArg i₁ (hϑz i)
      simp only [Fintype.sum_option, hz0, zero_mul, Finset.sum_const_zero, add_zero, map_mul, h1ϑ, u,
        Option.elim_none] at e
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      linear_combination -e)
    exact sub_eq_zero.1 this.1
  have hN : ∀ j, ∃ N : Option (Fin g) → W, (∀ o, i₀ (N o) = Option.elim o (c₀ j) (fun l => a₀ * M₀ j l)) ∧
      ∀ i, J i j = ∑ o, N o * u i o := by
    intro j
    exact GlobalTheory.T.coordinates_integral_of_linearly_independent_reduction W K₀ K₁ i₀ i₁ hi₀ hi₁ I (Option (Fin g)) u hind' (fun i => J i j) _ (fun i => by
      simp [Fintype.sum_option, u, h0J, Finset.mul_sum, _root_.mul_assoc]; ring)
  choose N hN0 hNJ using hN
  have hN1 : ∀ j l, i₁ (N j (some l)) = a₁ * M₁ j l := by
    intro j
    have := hind (i₁ (N j none) - c₁ j) (fun l => i₁ (N j (some l)) - a₁ * M₁ j l) (fun i => by
      have e := congrArg i₁ (hNJ j i)
      rw [h1J] at e
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_option, u, Option.elim_none, Option.elim_some, map_add (f := _), map_sum, map_mul, Finset.mul_sum] at e
      simp only [sub_mul, Finset.sum_sub_distrib, _root_.mul_assoc]
      linear_combination -e)
    intro l
    exact sub_eq_zero.1 (congrFun this.2 l)
  obtain ⟨v, hv⟩ := hi₁ (z none) (by rw [ha]; exact ha₁)
  have hne₀ : a₀ ≠ 0 := by rw [← ha₀, ← hv]; exact (v.map i₀.toMonoidHom).ne_zero
  refine ⟨z none, Matrix.of fun j l => ↑v⁻¹ * N j (some l), ha₀, ha, ?_, ?_⟩
  · ext j l
    have h1 : i₀ (↑v⁻¹ : W) = a₀⁻¹ := by
      rw [← ha₀, ← hv]; exact map_units_inv i₀ v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_mul, h1, Option.elim_some, hN0]
    field_simp
  · ext j l
    have h1 : i₁ (↑v⁻¹ : W) = a₁⁻¹ := by
      rw [← ha, ← hv]; exact map_units_inv i₁ v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_mul, h1, Option.elim_some, hN1]
    field_simp

theorem thJet_frameChange_castDim {K : Type} [Field K] [CharZero K] (x : KeyIn K) (th : x.P.L.Sec) (hth) (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv)
    (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K)
    (hth' : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ a * LB.Sec.f th i) (hv' : ∀ i, IsLieComb (M i) v (x.v i))
    {g : ℕ} (hg : x.P.g = g) (m : ℕ) (hm : Odd m) {I : Type} (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ ϑ' : I → K)
    (J J' : I → Fin g → K)
    (h1 : ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ hg m pt ϑ J) (h2 : ThJet x hg m pt ϑ' J') :
    (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin g → K, ∀ i j,
      J' i j = a * ∑ l, M.reindex (finCongr hg) (finCongr hg) j l * J i l + c j * ϑ i := by
  cases x
  subst hg
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; exact (Nat.not_odd_zero hm))
  simpa using GlobalTheory.T.thetaConstants_jets_change_section_basis K _ _ _ _ th hth v hv _ _ _ _ a M hth' hv' m hm hm0 I pt ϑ ϑ' J J' h1 h2

theorem keyValue_twoFibres : ∀ κ : Rule, Rule4 κ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] [IsIntegrallyClosed W] [CharZero W] (K₀ K₁ : Type) [Field K₀] [CharZero K₀] [Field K₁] [IsAlgClosed K₁] [CharZero K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (P : PolAV (Sp W)) (x₀ : KeyIn K₀) (x₁ : KeyIn K₁) (g : ℕ) (h₀ : x₀.P.g = g) (h₁ : x₁.P.g = g) (m : ℕ), P.g = g → Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ P.A)) (p₀ : I → (baseOver (Sp K₀) ⟶ x₀.P.A)) (p₁ : I → (baseOver (Sp K₁) ⟶ x₁.P.A)) (φ₀ : x₀.P.A.left ⟶ P.A.left) (φ₁ : x₁.P.A.left ⟶ P.A.left), (∀ a, pt a ^ (m ^ 2) = 1) → IsGrpPullback x₀.P.A P.A (spMap i₀) φ₀ → IsGrpPullback x₁.P.A P.A (spMap i₁) φ₁ → LBIso x₀.P.L (P.L.pull φ₀) → LBIso x₁.P.L (P.L.pull φ₁) → (∀ a, (p₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) → (∀ a, (p₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left) → (∀ z : baseOver (Sp K₁) ⟶ x₁.P.A, z ^ (m ^ 2) = 1 → ∃ a, p₁ a = z) → ∀ (ϑ : I → W) (J : I → Fin g → W) (k : W), ThJet x₀ h₀ m p₀ (fun a => i₀ (ϑ a)) (fun a j => i₀ (J a j)) → ThJet x₁ h₁ m p₁ (fun a => i₁ (ϑ a)) (fun a j => i₁ (J a j)) → (κ K₀ x₀ : K₀) = i₀ k → (κ K₁ x₁ : K₁) = i₁ k := by
  intro κ hκ W _ _ _ _ _ _ K₀ K₁ _ _ _ _ _ i₀ i₁ hi₀ hi₁ P x₀ x₁ g h₀ h₁ m hP hm hm3 I pt p₀ p₁ φ₀ φ₁ hpt hpb₀ hpb₁
    hL₀ hL₁ hc₀ hc₁ hsurj ϑ J k hJ₀ hJ₁ hk
  obtain ⟨hHom, -, -, hFam⟩ := hκ
  have hPg : 1 ≤ P.g := hP ▸ h₀ ▸ x₀.g_pos
  obtain ⟨y, rfl⟩ := GlobalTheory.T.exists_keyDatum_polarisedAbelian_localDomain W P hPg
  have hmu : IsUnit (m : W) := hi₁ _ (by rw [map_natCast]; exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨ϑ', J', hy⟩ := GlobalTheory.T.exists_thetaConstantsJets_localDomain W y g hP m hm hmu I pt hpt
  obtain ⟨th₀, hth₀, v₀, hv₀, hA₀⟩ := GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback W K₀ i₀ y x₀.P φ₀ x₀.g_pos x₀.rig x₀.rig_gen (h₀.trans hP.symm) hpb₀ hL₀
  obtain ⟨th₁, hth₁, v₁, hv₁, hA₁⟩ := GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback W K₁ i₁ y x₁.P φ₁ x₁.g_pos x₁.rig x₁.rig_gen (h₁.trans hP.symm) hpb₁ hL₁
  have hJy₀ := GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum W K₀ i₀ y ⟨x₀.P, x₀.g_pos, x₀.rig, x₀.rig_gen, th₀, hth₀, v₀, hv₀⟩ φ₀ hA₀ g hP h₀ m I pt p₀ ϑ' J' hc₀ hy
  have hJy₁ := GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum W K₁ i₁ y ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ φ₁ hA₁ g hP h₁ m I pt p₁ ϑ' J' hc₁ hy
  obtain ⟨a₀, M₀, ha₀, hth0, hv0⟩ := GlobalTheory.T.exists_scalar_matrix_between_keyData K₀ x₀.P th₀ x₀.th v₀ x₀.v hth₀ x₀.th_ne hv₀ x₀.basis
  obtain ⟨a₁, M₁, ha₁, hth1, hv1⟩ := GlobalTheory.T.exists_scalar_matrix_between_keyData K₁ x₁.P th₁ x₁.th v₁ x₁.v hth₁ x₁.th_ne hv₁ x₁.basis
  obtain ⟨hu0ϑ, c₀, hu0J⟩ := thJet_frameChange_castDim x₀ th₀ hth₀ v₀ hv₀ a₀ M₀ hth0 hv0 h₀ m hm p₀ _ _ _ _ hJy₀ hJ₀
  obtain ⟨hu1ϑ, c₁, hu1J⟩ := thJet_frameChange_castDim x₁ th₁ hth₁ v₁ hv₁ a₁ M₁ hth1 hv1 h₁ m hm p₁ _ _ _ _ hJy₁ hJ₁
  have hind := GlobalTheory.T.thetaConstants_firstJets_linearIndependent K₁ ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ g h₁ m hm hm3 I p₁ hsurj _ _ hJy₁
  obtain ⟨u, hu⟩ := hFam W y
  have hκy₀ := hu K₀ i₀ ⟨x₀.P, x₀.g_pos, x₀.rig, x₀.rig_gen, th₀, hth₀, v₀, hv₀⟩ ⟨φ₀, hA₀⟩
  have hκy₁ := hu K₁ i₁ ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ ⟨φ₁, hA₁⟩
  have hH₀ := hHom K₀ x₀.P x₀.g_pos x₀.rig x₀.rig_gen th₀ hth₀ v₀ hv₀ x₀.th x₀.th_ne x₀.v x₀.basis a₀ M₀ hth0 hv0
  have hH₁ := hHom K₁ x₁.P x₁.g_pos x₁.rig x₁.rig_gen th₁ hth₁ v₁ hv₁ x₁.th x₁.th_ne x₁.v x₁.basis a₁ M₁ hth1 hv1
  obtain ⟨a, M, ha0, ha1, hM0, hM1⟩ := frame_coords_lift i₀ i₁ hi₀ hi₁ ϑ ϑ' J J' hind a₀ _ c₀ hu0ϑ hu0J a₁ _ c₁ ha₁ hu1ϑ hu1J
  have H₀ : a₀ ^ 8 * (κ K₀ x₀ : K₀) = M₀.det ^ 4 * i₀ u := by rw [← hκy₀]; simpa using hH₀
  have H₁ : a₁ ^ 8 * (κ K₁ x₁ : K₁) = M₁.det ^ 4 * i₁ u := by rw [← hκy₁]; simpa using hH₁
  have e0 : a ^ 8 * k = M.det ^ 4 * u := by
    apply hi₀
    rw [map_mul, map_mul, map_pow, map_pow, ha0, RingHom.map_det, hM0, Matrix.det_reindex_self, ← hk, H₀]
  have e1 := congrArg i₁ e0
  rw [map_mul, map_mul, map_pow, map_pow, ha1, RingHom.map_det, hM1, Matrix.det_reindex_self, ← H₁] at e1
  exact (mul_left_cancel₀ (pow_ne_zero 8 ha₁) e1).symm

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyValue_two_fibres_local_ring : ∀ κ : Rule, Rule4 κ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] [IsIntegrallyClosed W] [CharZero W] (K₀ K₁ : Type) [Field K₀] [CharZero K₀] [Field K₁] [IsAlgClosed K₁] [CharZero K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (P : PolAV (Sp W)) (x₀ : KeyIn K₀) (x₁ : KeyIn K₁) (g : ℕ) (h₀ : x₀.P.g = g) (h₁ : x₁.P.g = g) (m : ℕ), P.g = g → Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ P.A)) (p₀ : I → (baseOver (Sp K₀) ⟶ x₀.P.A)) (p₁ : I → (baseOver (Sp K₁) ⟶ x₁.P.A)) (φ₀ : x₀.P.A.left ⟶ P.A.left) (φ₁ : x₁.P.A.left ⟶ P.A.left), (∀ a, pt a ^ (m ^ 2) = 1) → IsGrpPullback x₀.P.A P.A (spMap i₀) φ₀ → IsGrpPullback x₁.P.A P.A (spMap i₁) φ₁ → LBIso x₀.P.L (P.L.pull φ₀) → LBIso x₁.P.L (P.L.pull φ₁) → (∀ a, (p₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) → (∀ a, (p₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left) → (∀ z : baseOver (Sp K₁) ⟶ x₁.P.A, z ^ (m ^ 2) = 1 → ∃ a, p₁ a = z) → ∀ (ϑ : I → W) (J : I → Fin g → W) (k : W), ThJet x₀ h₀ m p₀ (fun a => i₀ (ϑ a)) (fun a j => i₀ (J a j)) → ThJet x₁ h₁ m p₁ (fun a => i₁ (ϑ a)) (fun a j => i₁ (J a j)) → (κ K₀ x₀ : K₀) = i₀ k → (κ K₁ x₁ : K₁) = i₁ k := by
  first | exact @GlobalTheory.MBLow.keyValue_twoFibres | exact GlobalTheory.MBLow.keyValue_twoFibres | (intros; apply GlobalTheory.MBLow.keyValue_twoFibres <;> assumption)
end

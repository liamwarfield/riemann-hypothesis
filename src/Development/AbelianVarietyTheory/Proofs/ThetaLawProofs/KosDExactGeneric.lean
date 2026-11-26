module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZeros

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa
open EtBaseChange

theorem section_ext_of_apply_eq {K : Type} [Field K] {X : Scheme.{0}} (t : X ⟶ Sp K) (a b : Sp K ⟶ X)
    (ha : a ≫ t = 𝟙 _) (hb : b ≫ t = 𝟙 _) (p : Sp K) (h : a p = b p) : a = b := by
  obtain ⟨⟨y, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨y', β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢
  have hy : y = y' := by simpa using h
  subst hy
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at ha hb
  have h₁ := Spec.map_injective ha
  have h₂ := Spec.map_injective hb
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₁
  have e₂ : ∀ k, β.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₂
  have : α = β := by
    ext k
    have e₃ : c.hom (α.hom k) = k := α.hom.injective (e₁ _)
    exact (e₂ (α.hom k)).symm.trans (congrArg β.hom e₃)
  rw [this]

theorem etZ_of_jac_ne_zero : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro O K _ _ _ x x' f φ w n d hg s s' z ch hf ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs hz₁ hz₂ hz₃ hz₄ hz₅
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint K))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := K) (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → Kˣ := fun a => Units.map (valH (T := K) (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := K) (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l =
        f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := K) h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := K) q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := K) (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : K) ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber O) ((toUnit (epsR O) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : K) ^ n * TrivSqZeroExt.snd (valT (T := DualNumber K)
          ((toUnit (epsR K) ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR K) ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber K) (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber K) q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : K) ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hval⟩
  · have hne : f (jac x s (z a) (ch a)) ≠ 0 := fun h => hz₃ a (hf (h.trans (map_zero f).symm))
    exact isUnit_of_mul_isUnit_left (hjac a ▸ hne.isUnit)
  · have e₀ : (z' a).left = (z' a').left :=
      section_ext_of_apply_eq x'.P.A.hom (z' a).left (z' a').left (Over.w (z' a)) (Over.w (z' a')) p e
    have e₁ : spMap f ≫ (z a).left = spMap f ≫ (z a').left :=
      (hz' a).symm.trans ((congrArg (· ≫ φ) e₀).trans (hz' a'))
    have : IsDominant (spMap f) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot f).1 hf]; exact bot_le)⟩
    have : IsProper x.P.A.hom := x.P.isAb.proper
    exact h (hz₄ (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp O) x.P.A.hom
      ((Over.w (z a)).trans (Over.w (z a')).symm) (spMap f) e₁)))
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) ⟨x'.P.A.hom y, (congrArg (fun q => q y) hp.1.w).symm⟩
      fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp O)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

end GlobalTheory.KeyKa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transversal_zeros_of_jacobian_ne_zero_domain : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  first | exact @GlobalTheory.KeyKa.etZ_of_jac_ne_zero | exact GlobalTheory.KeyKa.etZ_of_jac_ne_zero | (intros; apply GlobalTheory.KeyKa.etZ_of_jac_ne_zero <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.KoszulGenExact

theorem exact_of_rescale {K Ix : Type} [CommRing K] [Fintype Ix] [DecidableEq Ix] (D D' h : Matrix Ix Ix K)
    (σ : Ix → Kˣ) (h1 : D' * h + h * D' = 1) (h2 : ∀ p q, D p q = σ p * D' p q)
    (h3 : ∀ p q, D' p q * ((σ q)⁻¹ : Kˣ) = D' p q) (v : Ix → K) (hv : D.mulVec v = 0) :
    ∃ w, D.mulVec w = v := by
  have key : ∀ (x : Ix → K) (p : Ix), D.mulVec x p = (σ p : K) * D'.mulVec x p := by
    intro x p
    simp only [Matrix.mulVec, dotProduct, h2, Finset.mul_sum, _root_.mul_assoc]
  have hD'v : D'.mulVec v = 0 := by
    funext p
    have hp := congrFun hv p
    rw [key] at hp
    exact (Units.mul_right_eq_zero (σ p)).mp hp
  have hcol : ∀ x : Ix → K, D'.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * x q) = D'.mulVec x := by
    intro x
    funext p
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← _root_.mul_assoc, h3]
  have hu : D'.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q) = 0 := by
    rw [hcol]
    exact hD'v
  have hback : D'.mulVec (h.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q)) = fun q => ((σ q)⁻¹ : Kˣ) * v q := by
    have e := congrArg (fun M => M.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q)) h1
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero, add_zero,
      Matrix.one_mulVec] at e
    exact e
  refine ⟨h.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q), ?_⟩
  funext p
  rw [key, hback]
  exact Units.mul_inv_cancel_left (σ p) (v p)

theorem exact_kosD_map {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {g g' d : ℕ} (hg : g' = g) (c : ℕ → ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin (c j ^ g)) (Fin (c j' ^ g)) O) (ev : ∀ j, Matrix (Fin d) (Fin (c j ^ g)) O)
    (m' : Fin g' → ∀ j j', Matrix (Fin (c j ^ g')) (Fin (c j' ^ g')) K)
    (ev' : ∀ j, Matrix (Fin d) (Fin (c j ^ g')) K) (u : Fin d → Kˣ)
    (hm : ∀ i j, j < g' → ∀ k k', m' i j (j + 1) k k' = f (m (i.cast hg) j (j + 1)
      (k.cast (congrArg (fun r => c j ^ r) hg)) (k'.cast (congrArg (fun r => c (j + 1) ^ r) hg))))
    (hev : ∀ a k, ev' 0 a k * u a = f (ev 0 a (k.cast (congrArg (fun r => c 0 ^ r) hg))))
    (t : K) (ht : TorsSq kdeg (kosD (N := fun j => c j ^ g') m' ev') t) (v)
    (hv : ((kosD (N := fun j => c j ^ g) m ev).map f).mulVec v = 0) :
    ∃ w, ((kosD (N := fun j => c j ^ g) m ev).map f).mulVec w = v := by
  subst hg
  obtain ⟨h, -, hh, -⟩ := ht
  have hm2 : ∀ (i : Fin g') (j j' : ℕ), j' = j + 1 → j < g' →
      ∀ k k', m' i j j' k k' = f (m i j j' k k') := by
    intro i j j' hj hlt k k'
    subst hj
    have e := hm i j hlt k k'
    simp only [Fin.cast_eq_self] at e
    exact e
  have hev2 : ∀ j : ℕ, j = 0 → ∀ a k, f (ev j a k) = (u a : K) * ev' j a k := by
    intro j hj a k
    subst hj
    have e := hev a k
    simp only [Fin.cast_eq_self] at e
    rw [← e, mul_comm]
  refine exact_of_rescale ((kosD m ev).map f) (kosD m' ev') h (Sum.elim (fun _ => 1) u) hh ?_ ?_ v hv
  · intro p q
    rcases p with ⟨P, kp⟩ | a <;> rcases q with ⟨Q, kq⟩ | b
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.map_apply, kosD, Sum.elim_inl, Units.val_one, _root_.one_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hc
      · obtain ⟨hi, hQ⟩ := hc
        have hQc : Q.card = P.card + 1 := by rw [hQ, Finset.card_insert_of_notMem hi]
        have hlt : P.card < g' := by
          have hle := Finset.card_le_univ (insert i P)
          rw [Finset.card_insert_of_notMem hi, Fintype.card_fin] at hle
          omega
        rw [hm2 i P.card Q.card hQc hlt]
        simp
      · simp
    · simp [kosD]
    · simp only [Matrix.map_apply, kosD, Sum.elim_inr]
      split_ifs with hQ
      · exact hev2 _ (by simp [hQ]) a kq
      · simp
    · simp [kosD]
  · intro p q
    rcases q with _ | b
    · simp
    · rcases p with _ | a <;> simp [kosD]

theorem kosD_exact_generic : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] (K : Type) [Field K] (f : O →+* K) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∀ v, ((kosD (N := (fun j => (l - j * n) ^ x.P.g)) m (fun j => Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))).map f).mulVec v = 0 → ∃ w, ((kosD (N := (fun j => (l - j * n) ^ x.P.g)) m (fun j => Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))).map f).mulVec w = v := by
  intro hL O _ _ _ _ K _ f x n l s b m d z ch hf hn hl hb hmul hz0 hs0 hjac hzi hcov v hv
  obtain ⟨x', φ, w, hg, s', b', m', hkv, hsv, hbv, hb', hmul', hm', -⟩ :=
    GlobalTheory.T.exists_keyData_baseChange_sections_matrices hL O K f x n l s b m hl hb hmul
  obtain ⟨z', ch', u, het, hval⟩ :=
    GlobalTheory.T.transversal_zeros_of_jacobian_ne_zero_domain O K x x' f φ w n d hg s s' z ch hf hkv hsv hz0 hs0 hjac hzi hcov
  have hl' : x'.P.g * n < l := by rw [hg]; exact hl
  obtain ⟨-, t, m'', hmul'', ht⟩ := GlobalTheory.T.exists_koszulTorsion_transversal_split_zeros hL K x' n l d s' b' z' ch' hn hl' hb' het
  refine exact_kosD_map f hg (fun j => l - j * n) m
    (fun j => Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a))) m''
    (fun j => Matrix.of fun a k => valT (T := K) (z' a).left (x'.P.L.U (ch' a)) ((b' j k).f (ch' a)))
    (fun a => u a ^ (l - 0 * n)) ?_ ?_ (t : K) ht v hv
  · intro i j hj k k'
    have hS := hb' j hj.le
      (GlobalTheory.KeyKa.KoszulCx.mulSec x'.P.L (GlobalTheory.KeyKa.KoszulCx.cast_step hl' hj) (s' i) (b' (j + 1) k'))
    have e := hS.unique (hmul'' i j hj k') (hmul' i j hj k')
    exact (congrFun e k).trans (hm' i j (j + 1) k k')
  · intro a k
    have e := hval (l - 0 * n) (b 0 (k.cast (congrArg (fun r => (l - 0 * n) ^ r) hg))) (b' 0 k) a (hbv 0 k)
    rw [Units.val_pow_eq_pow_val]
    exact e

end GlobalTheory.KeyKa.KoszulGenExact
end

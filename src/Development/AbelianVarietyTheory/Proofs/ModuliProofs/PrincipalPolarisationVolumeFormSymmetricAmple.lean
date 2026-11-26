module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.PrincipalNumerics

theorem sectionsFiniteDimension_one_trivial_transitions {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K)
    (hp : Function.Bijective p.appTop.hom) {M : LB X} (hM : M.IsLB) (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hc : ∀ (U : X.Opens) (a : K), constFn p U a = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) := fun U a => rfl
  have hb : Function.Bijective (fun a : K => p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
    hp.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨s, hs, hu⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun i => homOfLE le_top) hM.cover.ge t.f (fun i j => by
    have := t.compat i j
    rw [hg, Units.val_one, _root_.one_mul] at this
    exact this)
  obtain ⟨a, rfl⟩ := hb.2 s
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · rw [Fin.sum_univ_one, _root_.mul_one, hc]
    exact (hs j).symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine hb.1 (hu _ fun j => ?_)
    have := hb' j
    rw [Fin.sum_univ_one, _root_.mul_one, hc] at this
    exact this.symm

variable {K : Type} [Field K]

theorem vol_one [IsAlgClosed K] (hH : Out.GlobalSectionsRankAlgClosed) (hG : Out.GlobalFnsSt) (P : Out.PolAV (Sp K)) :
    Vol P.A.hom P.L P.g 1 := by
  refine ⟨fun e => if e = 0 then 1 else e ^ P.g, fun e => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · refine sectionsFiniteDimension_one_trivial_transitions _ (hG _ P.A P.isAb) (DVR.linComb_isLB _ P.isLB _ _) fun i j => ?_
      show ∏ _ : PUnit.{1}, (_ : Γ(P.A.left, LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) i ⊓
        LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) j)ˣ) ^ (0 : ℤ) = 1
      simp only [zpow_zero, Finset.prod_const_one]
    · simp only [if_neg he.ne']
      exact PowSec.exists_basis_sections hH K P e he
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with e he
    have : (e : ℝ) ^ P.g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 he.ne')
    rw [if_neg he.ne', Nat.cast_pow, div_self this]

theorem formIs_id (P : Out.PolAV (Sp K)) : FormIs P P.L (𝟙 P.A) := by
  refine ⟨inferInstance, ?_⟩
  rw [Category.comp_id]
  exact PolBaseChange.lbIso_refl (DVR.linComb_isLB _ P.isLB _ _)

theorem symB (hG : Out.GlobalFnsSt) (P : Out.PolAV (Sp K)) : SymB P.L := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  have le : ∀ j : (PUnit → P.L.ι) × P.L.ι, (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left).U j.1 ⊓ P.L.U j.2 ≤
      LB.wchart P.L (![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2] :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]
  refine gen_chartPull (h := 𝟙 _) (A' := LB.div (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) P.L)
    (A := LB.LinComb P.L (K := Fin 2) ![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] ![1, -1])
    ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' => ?_⟩ u hu
  refine (gm_div P.L (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans
    (Eq.trans ?_ (gm_linComb P.L _ _ (𝟙 _) y _ _ (le j hj) (le j' hj')).symm)
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm
  · exact (gm_pull_g P.L _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm
  · exact (zpow_neg_one _).symm

theorem mapDeg_id (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := MapDeg.id_one X

theorem exists_basis_of_pairing {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ y : G, y ^ k = 1 →
      ∃! c : Fin (2 * g) → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y := by
  have : NeZero k := ⟨hk.ne'⟩
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* Rˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing k g T R ze hk hz (fun x => Subtype.ext x.2)
    (fun d hd => by
      rw [← hc d hd]
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩,
        fun x => ⟨⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩
      obtain ⟨c, hc⟩ := hd
      show x.1 ^ _ = 1
      rw [hc, pow_mul, x.2, one_pow]) e (fun x => (hw' _ _ _ (halt _ x.2)).symm)
    (fun x hx => Subtype.ext (hnd _ x.2 fun y hy => by
      have h : w x ⟨y, hy⟩ = 1 := hx ⟨y, hy⟩
      exact h ▸ hw x ⟨y, hy⟩))
  have cm : ∀ a b : G, Commute a b := fun a b => _root_.mul_comm a b
  have tor : ∀ i, (v i).1 ^ k = 1 := fun i => (v i).2
  have inj := LevelOfPairing.injective_comb cm hW hmul hz (fun i => (v i).1) tor
    (fun i j => (show w (v i) (v j) = _ from hv i j) ▸ hw _ _)
  refine ⟨fun i => (v i).1, tor, fun y hy => ?_⟩
  obtain ⟨c, hcy⟩ := LevelOfPairing.surjective_comb cm hk.ne' _ tor (hc k dvd_rfl) inj y hy
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
  · simpa only [ZMod.val_cast_of_lt (c _).2] using hcy
  · have := inj (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hcy.symm)
    funext i
    rw [← this]
    exact (ZMod.natCast_zmod_val _).symm

theorem exists_torsBasis [IsAlgClosed K] (hL : Out.Laws) (P : Out.PolAV (Sp K)) (k : ℕ) (hk : (k : K) ≠ 0) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt := by
  have := P.isAb.comm
  let c : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := c.toMulEquiv.isDomain _
  have hk0 : k ≠ 0 := fun e => hk (by rw [e, Nat.cast_zero])
  have : NeZero (k : K) := ⟨hk⟩
  have : NeZero k := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K k
  have hζ' : IsPrimitiveRoot (c.symm ζ) k := hζ.map_of_injective c.symm.injective
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P k (Out.baseOver _)
  refine Exists.imp (fun pt h => ⟨Nat.pos_of_ne_zero hk0, h⟩) ?_
  exact exists_basis_of_pairing (G := Out.baseOver _ ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0)
    (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K (𝟙 _) (by
      obtain ⟨e, rfl⟩ := hd
      rw [Nat.cast_mul] at hk
      exact left_ne_zero_of_mul hk))
    (hζ'.isUnit_unit hk0) (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (hL.weilNondeg K P _ hk)

theorem actsBy_id (P : Out.PolAV (Sp K)) {k m : ℕ} (hk0 : 0 < k) (hk : k ≠ 1) (pt : Fin m → (Out.baseOver (Sp K) ⟶ P.A)) :
    ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k)) := by
  have := P.isAb.comm
  refine ⟨hk0, fun i => ?_⟩
  rw [Category.comp_id, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i (fun b _ hb => by
    rw [Matrix.one_apply_ne hb, ZMod.val_zero, pow_zero]) (fun h => absurd (Finset.mem_univ _) h),
    Matrix.one_apply_eq, ZMod.val_one'' hk, pow_one]

end GlobalTheory.PrincipalNumerics


open GlobalTheory.PrincipalNumerics in
theorem GlobalTheory.principal_polarisation_numerics : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  intro hL _ K _ _ P
  refine ⟨vol_one hL.globalSectionsRank hL.globalFns P, formIs_id P, symB hL.globalFns P, mapDeg_id _,
    GlobalTheory.veryAmple_lbPow hL.ample K P 4 le_rfl, fun k hk => ?_⟩
  obtain ⟨pt, hpt⟩ := exists_torsBasis hL P k hk
  exact ⟨pt, hpt, fun h => actsBy_id P hpt.pos h pt⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  first | exact @GlobalTheory.principal_polarisation_numerics | exact GlobalTheory.principal_polarisation_numerics | (intros; apply GlobalTheory.principal_polarisation_numerics <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def IsHeckeIsog (o o' : Obj D l b s) (p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o'.t.act.act a) ∧
  (∀ y : 𝟙_ (Over (Sp k)) ⟶ o'.t.G, ∃ x, x ≫ ψ = y) ∧ (∀ x, x ≫ ψ = 1 ↔ x ∈ C) ∧
  (∀ (n : ℕ) (x x' : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (c : kˣ), n.Coprime p → Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) →
    Out.WeilIs o'.t.G o'.t.PP.L n (x ≫ ψ) (x' ≫ ψ) (unitOn (c ^ (p ^ 2)))) ∧
  ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

theorem exists_inv_mod {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : ∃ p', p * p' ≡ 1 [MOD n] := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
    (by rintro rfl; exact h (dvd_zero p))
  exact ⟨m, hm⟩

theorem natCast_M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf h).1

theorem eq_of_modEq {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c) {n : ℕ}
    (hn : ∀ a, f (n • a) = 1) {p₁ p₂ : ℕ} (h : p₁ ≡ p₂ [MOD n]) (a : A) : f (p₁ • a) = f (p₂ • a) := by
  have key : ∀ q : ℕ, f (q • a) = f ((q % n) • a) := fun q => by
    conv_lhs => rw [← Nat.mod_add_div q n, add_nsmul, hf, mul_nsmul', hn, _root_.mul_one]
  rw [key p₁, key p₂, h]

theorem eta_M (o : Obj D l b s) (a : D.La) : o.eta (l.M • a) = 1 :=
  o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)

theorem modEq_of_inv {p p₁ p₂ n : ℕ} (h₁ : p * p₁ ≡ 1 [MOD n]) (h₂ : p * p₂ ≡ 1 [MOD n]) : p₁ ≡ p₂ [MOD n] := by
  calc p₁ = p₁ * 1 := (Nat.mul_one _).symm
    _ ≡ p₁ * (p * p₂) [MOD n] := h₂.symm.mul_left _
    _ = (p * p₁) * p₂ := by ring
    _ ≡ 1 * p₂ [MOD n] := h₁.mul_right _
    _ = p₂ := Nat.one_mul _

theorem comp_act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) {T : Over S}
    (x : T ⟶ G) (n : ℕ) : x ≫ a.act (n : O) = x ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero, left_eq_mul.1 h, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, a.add, MonObj.comp_mul, ih, a.one, Category.comp_id, pow_succ]


set_option maxHeartbeats 400000 in
theorem exists_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hTate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^ 2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n * p ^ 2) x y c → e' n (ψ x) (ψ y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a)))
    (hQuot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left))
    (hWeil : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) → Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' → Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d))
    (hLie : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n)
    (o : Obj D l b s) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)) (c₁ : ∀ x ∈ C, ∀ a, x ≫ o.t.act.act a ∈ C)
    (c₂ : ∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, (∀ a ∈ J, x ≫ o.t.act.act a = 1) → x ∈ C)
    (c₃ : ∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), x ≫ o.t.act.act a = 1)
    (c₄ : ∀ x ∈ C, ∀ y ∈ C, Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1)
    (c₅ : Nat.card C = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) :
    (∀ x ∈ C, x ^ p ^ 2 = 1) ∧ ∃ (o' : Obj D l b s) (ψ : o.t.G ⟶ o'.t.G), IsHeckeIsog o o' p C ψ ∧
      IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  have hC : ∀ x ∈ C, x ^ p ^ 2 = 1 := fun x hx => by
    rw [← comp_act_natCast o.t.act]
    refine c₃ x hx _ ?_
    rw [Nat.cast_pow, pow_two]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
    rwa [map_natCast] at this
  refine ⟨hC, ?_⟩
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨t', ψ, hpr, ham, hkt, hhom, hfin, het, hsur, hker, hlin, hiso⟩ :=
    hQuot E H k o.t _ p C hp.pos o.proper hdim o.ample o.ktriv c₁ hC c₄ c₅
  obtain ⟨g', hg'⟩ := exists_dim t'
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P' := polOf t' hpr ham hkt hg'
  have hab' := isAbelianScheme_of_proper t' hpr
  have := o.proper
  have hW := fun (n : ℤ) (T : Over (Sp k)) (x y : T ⟶ o.t.G) c c' =>
    hWeil _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hpow : IsMonHom (𝟙 o.t.G ^ p ^ 2) := by
    rw [← comp_act_natCast o.t.act, Category.id_comp]; exact o.t.act.hom _
  obtain ⟨gm₀, hgm⟩ := exists_fac hab.smooth ψ (𝟙 o.t.G ^ p ^ 2) fun x hx => by
    rw [MonObj.comp_pow, Category.comp_id]; exact hC x ((hker x).1 hx)
  have hgm₁ : ∀ (T : Over (Sp k)) (x : T ⟶ o.t.G), x ≫ ψ = 1 → x ^ p ^ 2 = 1 := fun T x hx => by
    calc x ^ p ^ 2 = (x ≫ ψ) ≫ gm₀ := by rw [Category.assoc, hgm, MonObj.comp_pow, Category.comp_id]
      _ = (1 ≫ ψ) ≫ gm₀ := by rw [hx, MonObj.one_comp ψ]
      _ = 1 := by rw [Category.assoc, hgm, MonObj.one_comp]
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  let o' : Obj D l b s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro K _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom K x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← hLie _ _ _ _ ψ o.t.act t'.act hhom het hlin K x τ]
          exact hdet τ
        have hK : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 := fun n hn => by
          have := ((b.unit n hn).map β).ne_zero
          rwa [map_natCast] at this
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have desc : ∀ (n : ℕ) (z : Over.mk x ⟶ o.t.G), 0 < n → z ^ n = 1 →
            ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ o.t.G, toUnit (Over.mk x) ≫ z₀ = z := fun n z hn hz =>
          exists_of_torsion hL.mulN P x (Nat.cast_ne_zero.2 hn.ne') (hK n hn) z hz
        have one : ∀ {G : Over (Sp k)} [GrpObj G] (z₀ : 𝟙_ (Over (Sp k)) ⟶ G),
            toUnit (Over.mk x) ≫ z₀ = 1 → z₀ = 1 := fun z₀ h =>
          toUnit_comp_injective x _ (h.trans (MonObj.comp_one _).symm)
        have kerd : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 → ∃ z₀ ∈ C, toUnit (Over.mk x) ≫ z₀ = z := fun z hz => by
          obtain ⟨z₀, rfl⟩ := desc _ z (pow_pos hp.pos 2) (hgm₁ _ z hz)
          exact ⟨z₀, (hker z₀).1 (one _ ((Category.assoc _ _ _).symm.trans hz)), rfl⟩
        have uniq : ∀ (n : ℕ) (z w : Over.mk x ⟶ o.t.G) (c c' : Kˣ), z ^ n = 1 → w ^ n = 1 →
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' hz hw h h' => (unitOn_bijective K).1 (((hL.weil _ P n _).1 z w hz hw).unique h h')
        have iso : ∀ z w : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 → w ≫ ψ = 1 →
            Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w (unitOn (1 : Kˣ)) := fun z w hz hw => by
          have h₁ : Out.WeilIs t'.G t'.PP.L ((1 : ℕ) : ℤ) (1 : Over.mk x ⟶ t'.G) 1 1 :=
            (hL.weil _ P' 1 (Over.mk x)).2.2.1 1 (one_pow _)
          have h₀ : Out.WeilIs t'.G t'.PP.L ((1 : ℕ) : ℤ) (z ≫ ψ) (w ≫ ψ) 1 := by rw [hz, hw]; exact h₁
          have h₂ := (hW ((1 : ℕ) : ℤ) _ z w 1 1 h₀).1
          rw [Nat.cast_one, _root_.one_mul] at h₂
          exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h₂
        obtain ⟨I', hζ', hev⟩ := hTate E H D 𝔓 p K _ _ _ (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z hz hz' => by
            obtain ⟨z₀, rfl⟩ := desc _ z hp.pos hz
            show (_ ≫ z₀) ≫ ψ = 1
            rw [Category.assoc, (hker z₀).2 (c₂ J hJ z₀ fun a ha =>
              one _ ((Category.assoc _ _ _).symm.trans (hz' a ha))), MonObj.comp_one])
          (fun z hz => ⟨hgm₁ _ z hz, fun a ha => by
            obtain ⟨z₀, h₀, rfl⟩ := kerd z hz
            show (_ ≫ z₀) ≫ _ = 1
            rw [Category.assoc, c₃ z₀ h₀ a ha, MonObj.comp_one]⟩)
          (fun z w hz hw => iso z w hz hw)
          (by
            rw [← c₅]
            refine (Nat.card_congr (Equiv.ofBijective (fun z : C => (⟨toUnit (Over.mk x) ≫ z.1, by
              show (_ ≫ z.1) ≫ ψ = 1
              rw [Category.assoc, (hker _).2 z.2, MonObj.comp_one]⟩ : ψx.ker)) ⟨fun a c h =>
                Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), fun z => ?_⟩)).symm
            obtain ⟨z₀, h₀, e⟩ := kerd z.1 z.2
            exact ⟨⟨z₀, h₀⟩, Subtype.ext e⟩)
          (fun n z w c c' _ hz hw h h' => uniq n z w c c' hz hw h h')
          (fun n z w c hn hz hw h => by
            obtain ⟨c', hc', -⟩ := (hL.weil _ P' n (Over.mk x)).1 (z ≫ ψ) (w ≫ ψ) hz hw
            obtain ⟨c', rfl⟩ := (unitOn_bijective K).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            have t : ∀ u : Over.mk x ⟶ o.t.G, ψx u ^ n = 1 → u ^ (n * p ^ 2) = 1 := fun u hu => by
              rw [pow_mul]; exact hgm₁ _ _ ((map_pow ψx u n).trans hu)
            rw [uniq _ z w c c' (t z hz) (t w hw) h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _), ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨hhom, hlin, fun y => exists_lift_pt ψ (𝟙 _) y, hker, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩,
    hfin, het, hsur⟩
  · have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (𝟙_ (Over (Sp k))).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P' n _).1 (x ≫ ψ) (x' ≫ ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (hW n _ x x' _ _ hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · have e := modEq_of_inv hp' hp₀
    exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add (eta_M o) (e.of_dvd hMM) a),
      congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory.HeckePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

noncomputable section

namespace GlobalTheory.SquareGenerated

section
variable {X Y : Scheme.{0}} {H : LB X}

theorem unitAt_of_mem (s : LB.Sec H) (φ : Y ⟶ X) (y : Y) (hy : φ y ∈ Out.nonzeroLocus s) :
    UnitAt H (K := Fin 1) (fun _ => φ) (fun _ => 1) y := by
  have v : ∀ (j : Fin 1 → H.ι) (z : Y), z ∈ LB.wchart H (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z (LB.wchart H (fun _ : Fin 1 => φ) j)
        ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))) = gs (𝟙 Y ≫ φ) z (H.U (j 0)) (s.f (j 0)) := fun j z hz =>
    (gs_res _ z _ hz _).trans (gs_pull _ φ z _ (LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz) _)
  let s' : LB.Sec (LB.LinComb H (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            (congrArg Units.val (gm_linComb H _ _ (𝟙 Y) z j j' hz.1 hz.2)))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        have hm : (𝟙 Y ≫ φ) z ∈ H.U (j 0) ⊓ H.U (j' 0) :=
          ⟨LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz.1, LB.wchart_le H (fun _ : Fin 1 => φ) j' 0 hz.2⟩
        refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res _ z _ hm _))))
        rw [gs_unit _ z _ hm, Fin.prod_univ_one, zpow_one] }
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => k) ?_⟩
  have hm : y ∈ LB.wchart H (fun _ : Fin 1 => φ) (fun _ => k) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ hk
  show y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op).hom
          ((φ.app _).hom (s.f k)))
  have e := Y.basicOpen_res ((φ.app _).hom (s.f k))
    (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op
  refine e ▸ ⟨hm, ?_⟩
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f k)) y).1 hk

theorem exists_sec_pw (hH : H.IsLB) (t : ℤ) (y : X)
    (h : UnitAt H (K := Fin 1) (fun _ => 𝟙 X) (fun _ => t) y) :
    ∃ u : LB.Sec (pw H t), y ∈ Out.nonzeroLocus u := by
  obtain ⟨s, hs⟩ := h
  have le : ∀ i : H.ι, H.U i ≤ LB.wchart H (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i z hz => Set.mem_iInter.2 fun _ => hz
  let u : LB.Sec (pw H t) :=
    { f := fun i => (X.presheaf.map (homOfLE (le i)).op).hom (s.f fun _ => i)
      compat := fun i j => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le i) hz.1 _)).trans
          (Eq.trans ?_ ((gs_mul (𝟙 X) z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 X) z _ hz _)
              ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le j) hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (le i hz.1) (le j hz.2)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
        exact (Fin.prod_univ_one _).trans (map_zpow _ _ _).symm }
  choose I hI using fun χ : X ⟶ X => exists_chart hH (χ y)
  have hm : y ∈ H.U (I (𝟙 X ≫ 𝟙 X)) := hI (𝟙 X ≫ 𝟙 X)
  refine ⟨u, TopologicalSpace.Opens.mem_iSup.2 ⟨I (𝟙 X ≫ 𝟙 X), (X.mem_basicOpen _ _ hm).2 ?_⟩⟩
  exact (congrArg IsUnit ((gs_eq (𝟙 X) y _ hm _).symm.trans (gs_res (𝟙 X) y (le _) hm _))).mpr (hs I hI)

end

theorem exists_sec_sq {O : Type} [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    {H : LB A.left} (hH : H.IsLB) (hT : Triv (Theta A H)) (s : LB.Sec H) (a : 𝟙_ (Over (Sp O)) ⟶ A)
    (y : A.left) (h₁ : ((toUnit A ≫ a) * 𝟙 A).left y ∈ Out.nonzeroLocus s)
    (h₂ : ((toUnit A ≫ a⁻¹) * 𝟙 A).left y ∈ Out.nonzeroLocus s) :
    ∃ u : LB.Sec (pw H 2), y ∈ Out.nonzeroLocus u := by
  obtain ⟨t, ht⟩ := hT
  let χ : Fin 4 → (Sp O ⟶ A.left) := ![(a * a⁻¹).left, a.left, (a⁻¹).left, (1 : 𝟙_ (Over (Sp O)) ⟶ A).left]
  choose i hi using fun k => exists_chart hH (χ k (IsLocalRing.closedPoint O))
  have e : ∀ k, (![((toUnit A ≫ a) * (toUnit A ≫ a⁻¹)).left, (toUnit A ≫ a).left,
      (toUnit A ≫ a⁻¹).left, (1 : A ⟶ A).left] k) = (toUnit A).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (toUnit A ≫ (a * a⁻¹)).left
      rw [MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (toUnit A ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := GlobalTheory.AbSquare.exists_gen_square hH t ht (toUnit A ≫ a) (toUnit A ≫ a⁻¹) (𝟙 A) i
    (fun k z => by
      rw [e k]
      have h : χ k ⁻¹ᵁ H.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
      show (toUnit A).left z ∈ χ k ⁻¹ᵁ H.U (i k)
      rw [h]; trivial)
  have hu' : UnitAt H _ _ y := ⟨genSec u hu, fun J hJ => by
    rw [sval_genSec u hu _ y hJ]; exact Units.isUnit _⟩
  have e1 : (toUnit A ≫ a) * (toUnit A ≫ a⁻¹) * 𝟙 A = 𝟙 A := by
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
  refine exists_sec_pw hH 2 y (UnitAt.congr hH (formEq_of_add fun U _ hh => ?_)
    (((unitAt_of_mem s _ y h₁).mul (unitAt_of_mem s _ y h₂)).mul hu'))
  simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, e1, Sum.elim_inl, Sum.elim_inr]
  simp
  module

theorem exists_secs_sq_generate : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro O K _ _ _ _ _ _ _ A _ _ hA H hH hT s hs
  obtain ⟨-, hk, hlift⟩ := GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift O K
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let t : Sp (IsLocalRing.ResidueField O) ⟶ Sp O := spMap (IsLocalRing.residue O)
  let T : Over (Sp O) := Over.mk t
  have : IsIntegral (T ⊗ A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.hom).flip
  let p : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint (IsLocalRing.ResidueField O)
  have htp : t p = IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have up : ∀ x : A.left, A.hom x = IsLocalRing.closedPoint O → ∃ z : (T ⊗ A).left, (snd T A).left z = x := by
    intro x hx
    have : x ∈ Set.range (pullback.snd t A.hom) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨p, htp.trans hx.symm⟩
    exact this
  let W : A.left.Opens := ⨆ u : LB.Sec (pw H 2), Out.nonzeroLocus u
  have hW : W = ⊤ := by
    by_contra hne
    have hZ : ((W : Set A.left)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (SetLike.coe_injective h)
    have hc : IsClosed (A.hom '' (W : Set A.left)ᶜ) := A.hom.isClosedMap _ W.isOpen.isClosed_compl
    obtain ⟨x₀, hx₀, hx₁⟩ : IsLocalRing.closedPoint O ∈ A.hom '' (W : Set A.left)ᶜ := by
      obtain ⟨q, hq⟩ := hZ.image A.hom
      exact (IsLocalRing.specializes_closedPoint q).mem_closed hc hq
    obtain ⟨z₀, hz₀⟩ := up x₀ hx₁
    have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left :=
      inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
    have : JacobsonSpace (T ⊗ A).left :=
      LocallyOfFiniteType.jacobsonSpace (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left
    obtain ⟨c, hcZ, hcc⟩ := nonempty_inter_closedPoints
      (Z := (((snd T A).left ⁻¹ᵁ W : (T ⊗ A).left.Opens) : Set (T ⊗ A).left)ᶜ)
      ⟨z₀, by
        show ¬ (snd T A).left z₀ ∈ W
        rw [hz₀]; exact hx₀⟩ ((snd T A).left ⁻¹ᵁ W).isOpen.isClosed_compl.isLocallyClosed
    let σ := pointOfClosedPoint (X := (T ⊗ A).left) (K := IsLocalRing.ResidueField O) (fst T A).left c hcc
    have hσ : σ ≫ (fst T A).left = 𝟙 _ := pointOfClosedPoint_comp _ c hcc
    have hσp : σ p = c := pointOfClosedPoint_apply _ c hcc p
    let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
      rw [← Over.w (fst T A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
    let x : T ⟶ A := σ' ≫ snd T A
    have hx : x.left p ∉ W := by
      show (snd T A).left (σ p) ∉ W
      rw [hσp]; exact hcZ
    obtain ⟨y₀, hy₀, hy₁⟩ := hs
    obtain ⟨z₁, hz₁⟩ := up y₀ hy₁
    obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t ((snd T A).left ⁻¹ᵁ Out.nonzeroLocus s)
      ⟨z₁, by
        show (snd T A).left z₁ ∈ Out.nonzeroLocus s
        rw [hz₁]; exact hy₀⟩ x x
    obtain ⟨b, hb, hba⟩ := hlift A.left A.hom inferInstance a.left (Over.w a)
    let b' : 𝟙_ (Over (Sp O)) ⟶ A := Over.homMk b hb
    have hb' : toUnit T ≫ b' = a := Over.OverMorphism.ext hba
    have key : ∀ (d : 𝟙_ (Over (Sp O)) ⟶ A), (Out.ptSecT A ((toUnit T ≫ d) * x)).left p ∈
        (snd T A).left ⁻¹ᵁ Out.nonzeroLocus s →
        ((toUnit A ≫ d) * 𝟙 A).left (x.left p) ∈ Out.nonzeroLocus s := by
      intro d hd
      have e : x ≫ ((toUnit A ≫ d) * 𝟙 A) = Out.ptSecT A ((toUnit T ≫ d) * x) ≫ snd T A := by
        simp [Out.ptSecT, MonObj.comp_mul]
      have e' : ((toUnit A ≫ d) * 𝟙 A).left (x.left p) =
          (snd T A).left ((Out.ptSecT A ((toUnit T ≫ d) * x)).left p) :=
        congrArg (fun q => q.left p) e
      rw [e']; exact hd
    obtain ⟨u, hu⟩ := exists_sec_sq A hH hT s b' (x.left p) (key b' (by rw [hb']; exact h₁ p))
      (key b'⁻¹ (by rw [GrpObj.comp_inv, hb']; exact h₂ p))
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨u, hu⟩)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec (pw H 2) => (Out.nonzeroLocus u : Set A.left)) (fun u => (Out.nonzeroLocus u).isOpen)
    (fun y _ => by
      have : y ∈ W := by rw [hW]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i : LB.Sec (pw H 2))), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end GlobalTheory.SquareGenerated
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_generate_square_bundle : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.SquareGenerated.exists_secs_sq_generate | exact GlobalTheory.SquareGenerated.exists_secs_sq_generate | (intros; apply GlobalTheory.SquareGenerated.exists_secs_sq_generate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjTheta

theorem prod_ev {M Q : Type} [AddCommGroup M] [Group Q] {m : ℕ} (ev : M → Q) (add : ∀ a c, ev (a + c) = ev a * ev c)
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] M) (c : Fin m → ℕ) :
    (List.ofFn fun i => ev (bas (Pi.single i 1)) ^ c i).prod = ev (bas fun i => (c i : ℤ)) := by
  let f : Multiplicative M →* Q := MonoidHom.mk' (fun x => ev x.toAdd) fun a b => add _ _
  have h : (fun i => ev (bas (Pi.single i 1)) ^ c i) =
      f ∘ fun i => Multiplicative.ofAdd (bas (Pi.single i 1)) ^ c i := by
    funext i
    exact (map_pow f (Multiplicative.ofAdd (bas (Pi.single i 1))) (c i)).symm
  rw [h, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
  show ev _ = _
  congr 1
  rw [toAdd_prod]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [toAdd_pow, toAdd_ofAdd, ← map_nsmul, ← map_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem ev_pow {M Q : Type} [AddCommGroup M] [Group Q] (ev : M → Q) (add : ∀ a c, ev (a + c) = ev a * ev c)
    (n : ℕ) (a : M) : ev a ^ n = ev (n • a) :=
  (map_pow (MonoidHom.mk' (fun x : Multiplicative M => ev x.toAdd) fun _ _ => add _ _) (Multiplicative.ofAdd a) n).symm

theorem existsUnique_label {M Q : Type} [AddCommGroup M] [Group Q] {m n : ℕ} (hn : 0 < n) (ev : M → Q)
    (add : ∀ a c, ev (a + c) = ev a * ev c) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] M) {y : Q} (hy : ∃ a, ev a = y) :
    ∃! c : Fin m → ZMod n, (List.ofFn fun i => ev (bas (Pi.single i 1)) ^ (c i).val).prod = y := by
  have : NeZero n := ⟨hn.ne'⟩
  have key : ∀ u v : Fin m → ℤ, ev (bas u) = ev (bas v) ↔ ∀ i, (u i : ZMod n) = v i := by
    intro u v
    have e : ev (bas u) = ev (bas (u - v)) * ev (bas v) := by rw [← add, ← map_add (f := _), sub_add_cancel]
    rw [e, mul_eq_right, ker]
    constructor
    · rintro ⟨b, hb⟩ i
      obtain ⟨w, rfl⟩ := bas.surjective b
      rw [← map_nsmul] at hb
      have := congrFun (bas.injective hb) i
      simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at this
      rw [← sub_eq_zero, ← Int.cast_sub, this]
      simp
    · intro h
      have : ∀ i, ∃ w : ℤ, u i - v i = n * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [Int.cast_sub, h, sub_self])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨u, rfl⟩ := bas.surjective a
  refine ⟨fun i => (u i : ZMod n), ?_, fun c hc => ?_⟩
  · beta_reduce
    rw [prod_ev ev add, key]
    intro i
    simp
  · beta_reduce at hc
    rw [prod_ev ev add, key] at hc
    funext i
    simpa using hc i

theorem root_ext {S : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {u v : Γ(S, ⊤)ˣ} (hu : u ^ n = 1) (hv : v ^ n = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      Units.map x.appTop.hom.toMonoidHom u = Units.map x.appTop.hom.toMonoidHom v) : u = v := by
  let w : Γ(S, ⊤) := (u * v⁻¹ : Γ(S, ⊤)ˣ)
  have hw : w ^ n = 1 := by
    have : (u * v⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hu, hv, inv_one, _root_.mul_one]
    exact congrArg Units.val this
  have unit : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    refine RingedSpace.isUnit_of_isUnit_germ S.toLocallyRingedSpace.toRingedSpace ⊤ _ fun p hp => ?_
    refine (S.mem_basicOpen _ p hp).1 ?_
    let K := AlgebraicClosure (S.residueField p)
    let x : Sp K ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) K)) ≫ S.fromSpecResidueField p
    have hx : x (default : PrimeSpectrum K) = p := Scheme.fromSpecResidueField_apply p _
    have h1 : x.appTop.hom w = 1 := by
      have : Units.map x.appTop.hom.toMonoidHom (u * v⁻¹) = 1 := by
        rw [map_mul, map_inv, h K x, mul_inv_cancel]
      exact congrArg Units.val this
    have h2 : IsUnit (x.appTop.hom (∑ i ∈ Finset.range n, w ^ i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
      simpa using hn.map x.appTop.hom
    have h3 : x ⁻¹ᵁ S.basicOpen (∑ i ∈ Finset.range n, w ^ i) = ⊤ := by
      rw [Scheme.preimage_basicOpen_top]
      exact Scheme.basicOpen_of_isUnit _ h2
    rw [← hx]
    exact (h3.ge : _) (Set.mem_univ (default : PrimeSpectrum K))
  have h0 : w - 1 = 0 := by
    have := geom_sum_mul w n
    rw [hw, sub_self] at this
    exact (unit.mul_right_eq_zero).1 this
  exact mul_inv_eq_one.1 (Units.ext (sub_eq_zero.1 h0))

theorem exists_weilIs_root (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (P : Out.PolAV S) (t : LB.Gen (Theta P.A P.L))
    (ht : t.IsGen) (n : ℕ) {T : Over S} {x y : T ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, Out.WeilIs P.A P.L n x y c ∧ c ^ n = 1 := by
  have := P.isAb.comm
  have loc : ∀ z : T ⟶ P.A, z ^ n = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨V, hV, H⟩ := (KerPow.locGen_theta_iff P.isLB P.ktriv
      (fun a c => (KerPow.locGen_iff _ _ _).1 (AbSquare.square_local P.isLB t ht T a c)) z n).2 hz p
    exact ⟨V, hV, KerPow.exists_theta z n V H⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG P.isAb P.isLB (loc x hx) (loc y hy)
  have pw : ∀ m : ℕ, Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih => rw [pow_succ x (m + 1), pow_succ c (m + 1)]; exact weilIs_mul_left hG S P n T _ _ _ _ _ ih hc
  have e := pw n
  rw [pow_succ x, hx, _root_.one_mul] at e
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB e hc
  rw [pow_succ, mul_eq_right] at this
  exact ⟨c, hc, this⟩

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  have e₁ := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  have e₂ := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e₁ e₂
  exact e₁.trans e₂.symm

theorem exists_tObj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (ρ : o) (j : o →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (ob : Obj D l bB s), IsSympBasis D bas → j ρ = bB.ρ → j (b.ζ : o) = bB.ζ → ∃ t : TObj g l.A J b (s ≫ spMap j), ObjUnder ob a bas t ∧ IsPEL D a bas ρ t ob.t := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b ρ j S s ob hbas hρ hζ
  have hG := hL.globalFns
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have h₁ := finrank_int_lattice D
    have h₂ := bas.finrank_eq
    rw [Module.finrank_fin_fun] at h₂
    omega
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ ob.t.G) := fun i => toUnit _ ≫ ob.etaA (bas (Pi.single i 1))
  have hpt : ∀ (T : Over S) (f : T ⟶ Out.baseOver S) (i), f ≫ pt i = toUnit T ≫ ob.etaA (bas (Pi.single i 1)) :=
    fun T f i => by rw [← Category.assoc, comp_toUnit]
  have tors : ∀ i, pt i ^ l.A = 1 := fun i => by
    rw [← MonObj.comp_pow, ev_pow ob.etaA ob.etaA_add, ob.etaA_ker, MonObj.comp_one]
  have hβ : ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x ≫ s = spMap (Spec.preimage (x ≫ s)).hom :=
    fun K _ x => (Spec.map_preimage (x ≫ s)).symm
  have hiso : LBIso ob.t.PP.L (ob.t.PP.L.pull (𝟙 ob.t.G.left)) := by
    let X := ob.t.G.left
    let L : LB X := ob.t.PP.L
    let M := L.pull (𝟙 X)
    have chart_le (i : M.ι) : M.U i ≤ L.U (i PUnit.unit) := fun _ hi => mem_pull.1 hi
    have transition (i j : M.ι) {W : X.Opens} (h : W ≤ M.U i ⊓ M.U j) :
        res h (M.g i j) =
          res (h.trans (inf_le_inf (chart_le i) (chart_le j))) (L.g (i PUnit.unit) (j PUnit.unit)) := by
      refine (LB.res_lcg L (fun _ : PUnit => 𝟙 X) (fun _ => 1) i j h).trans ?_
      rw [Fintype.prod_unique, zpow_one] <;> exact Units.ext rfl
    let N := M.div L
    have overlap_le (p : N.ι) : N.U p ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 :=
      inf_le_inf (chart_le p.1) le_rfl
    refine ⟨⟨fun p => res (overlap_le p) (L.g (p.1 PUnit.unit) p.2)⟩, ?_⟩
    intro p q
    let W := N.U p ⊓ N.U q
    have hp₁ : W ≤ L.U (p.1 PUnit.unit) := inf_le_left.trans ((overlap_le p).trans inf_le_left)
    have hp₂ : W ≤ L.U p.2 := inf_le_left.trans inf_le_right
    have hq₁ : W ≤ L.U (q.1 PUnit.unit) := inf_le_right.trans ((overlap_le q).trans inf_le_left)
    have hq₂ : W ≤ L.U q.2 := inf_le_right.trans inf_le_right
    have hM : W ≤ M.U p.1 ⊓ M.U q.1 :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    change res (show W ≤ N.U p from inf_le_left) (res (overlap_le p) (L.g (p.1 PUnit.unit) p.2)) =
      (res hM (M.g p.1 q.1) * (res (le_inf hp₂ hq₂) (L.g p.2 q.2))⁻¹) *
        res (show W ≤ N.U q from inf_le_right) (res (overlap_le q) (L.g (q.1 PUnit.unit) q.2))
    have hL : L.IsLB := ob.t.PP.isLB
    have hc₁ := LB.res_cocycle hL (p.1 PUnit.unit) (q.1 PUnit.unit) q.2
      (le_inf hp₁ hq₁) (le_inf hq₁ hq₂) (le_inf hp₁ hq₂)
    have hc₂ := LB.res_cocycle hL (p.1 PUnit.unit) p.2 q.2
      (le_inf hp₁ hp₂) (le_inf hp₂ hq₂) (le_inf hp₁ hq₂)
    rw [LB.res_res, LB.res_res, transition, mul_right_comm, hc₁, ← hc₂, mul_inv_cancel_right]
  refine ⟨{ A := ob.t.G
            ab := ObjDim.isAbelianScheme ob
            dim := hg ▸ ObjDim.smoothOfRelativeDimension ob
            L := ob.t.PP.L
            isLB := ob.t.PP.isLB
            rigid := ObjDim.rigidified
            sym := ObjDim.sym
            ample := ob.ample
            ktriv := ob.ktriv
            pt := pt
            torsion := tors
            bij := fun K _ _ x y hy => ?_
            pairing := fun i i' => ?_
            act := fun c => ob.t.act.act (a c)
            hom := fun c => ob.t.act.hom (a c) },
    ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 ob.t.G)), hiso,
      fun c => (Category.comp_id _).trans (Category.id_comp _).symm, fun i => ?_⟩,
    ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 ob.t.G)), hiso,
      fun c => (Category.comp_id _).trans (Category.id_comp _).symm, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨-, I, -, hI, -⟩ := ob.geom K x _ (hβ K x)
    simp only [hpt, hI]
    exact existsUnique_label l.A_pos (I.ev l.A) (I.add l.A) (I.ker l.A l.A_pos) bas ((I.onto l.A l.A_pos y).1 hy)
  · obtain ⟨c, hc, hcn⟩ := exists_weilIs_root hG (Obj.toPolAV ob) ob.t.cub.t ob.t.cub.isGen l.A (tors i) (tors i')
    have hu : IsUnit ((l.A : ℕ) : Γ(S, ⊤)) := by
      simpa using ((bB.unit l.A l.A_pos).map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).map s.appTop.hom
    have hz : unitS (s ≫ spMap j) b.ζ ^ l.A = 1 := by
      have e := map_unitS (spMap j) (𝟙 _) j (Category.id_comp _) b.ζ
      have e₀ : Units.map j.toMonoidHom b.ζ ^ l.A = 1 := Units.ext (by
        show j b.ζ ^ l.A = 1
        rw [hζ, bB.ζ_prim.pow_eq_one])
      have e₁ : unitS (s ≫ spMap j) b.ζ = Units.map s.appTop.hom.toMonoidHom (unitOn (Units.map j.toMonoidHom b.ζ)) := by
        rw [← e]
        apply Units.ext
        simp [unitS]
        rfl
      rw [e₁, ← map_pow, unitOn, ← map_pow, e₀, map_one, map_one]
    have : c = unitS (s ≫ spMap j) b.ζ ^ Out.stdSymp g i i' := by
      refine root_ext (S := S) hu hcn (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow])
        fun K _ _ x => ?_
      obtain ⟨-, I, hIζ, hI, -⟩ := ob.geom K x _ (hβ K x)
      have h₁ := CommPairing.weilIs_pull hG (ObjDim.isAbelianScheme ob) ob.t.PP.isLB
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) hc
      rw [hpt, hpt, hI, hI] at h₁
      have h₂ := I.isom l.A l.A_pos (bas (Pi.single i 1)) (bas (Pi.single i' 1))
      refine (CommutatorPairing.weilIs_unique hG (ObjDim.isAbelianScheme ob) ob.t.PP.isLB h₁ h₂).trans ?_
      rw [hbas, map_zpow, map_unitS (s ≫ spMap j) x ((Spec.preimage (x ≫ s)).hom.comp j)
        (by rw [← Category.assoc, Geo.Tor.spMap_comp, ← hβ K x]), unitOn, unitOn, map_zpow]
      congr 2
      exact Units.ext (hIζ.trans (congrArg _ hζ.symm))
    exact this ▸ hc
  · have e : (toUnit (Out.baseOver S)).left = 𝟙 S :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (Out.baseOver S)))
    show (ob.etaA _).left ≫ 𝟙 _ = (toUnit (Out.baseOver S)).left ≫ (ob.etaA _).left
    rw [e]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have e : (Spec.preimage (x ≫ s)).hom.comp j = β := by
      have : spMap ((Spec.preimage (x ≫ s)).hom.comp j) = spMap β := by
        rw [Geo.Tor.spMap_comp, ← hβ K x, Category.assoc, hx]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have e₁ : (Spec.preimage (x ≫ s)).hom bB.ρ = β ρ := by rw [← hρ]; exact RingHom.congr_fun e ρ
    have e₂ : (Spec.preimage (x ≫ s)).hom bB.ζ = β b.ζ := by rw [← hζ]; exact RingHom.congr_fun e b.ζ
    have hx' := ob.geom K x _ (hβ K x)
    rw [e₁, e₂] at hx'
    obtain ⟨hd, I, hIζ, hI, -⟩ := hx'
    refine ⟨hd, I, hIζ, fun i => ?_⟩
    exact (Category.comp_id _).trans ((hI _).symm.trans (hpt _ _ i).symm)

end GlobalTheory.ObjTheta
end

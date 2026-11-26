module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
noncomputable section

open NumberField UpperTheory.V.KL

namespace UpperTheory.V.ZK.Up

def rq (q : ℕ) (G : Type) (m : ℕ) : Ch ℤ G m →+ Ch (ZMod q) G m :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod q))

structure IsCls (k : ℕ) (cls : ∀ (G : Type) [Group G], LinearMap.ker (bd ℤ G k) →+ grpH G (k + 1)) : Prop where
  surj : ∀ (G : Type) [Group G], Function.Surjective (cls G)
  zero : ∀ (G : Type) [Group G] (z : LinearMap.ker (bd ℤ G k)), cls G z = 0 ↔ Bd z.1
  nat : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (z : LinearMap.ker (bd ℤ G k)) (z' : LinearMap.ker (bd ℤ H k)),
    z'.1 = cm ℤ f (k + 1) z.1 → cls H z' = (grpHMap f (k + 1)).hom (cls G z)

def Bridge : Prop := ∀ k : ℕ, ∃ cls, IsCls k cls

def RqFacts : Prop :=
  ∀ q : ℕ,
    (∀ (G : Type) [Group G] (m : ℕ) (z : Ch ℤ G (m + 1)), bd (ZMod q) G m (rq q G (m + 1) z) = rq q G m (bd ℤ G m z)) ∧
    (∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch ℤ G m),
      cm (ZMod q) f m (rq q G m z) = rq q H m (cm ℤ f m z)) ∧
    (∀ (G : Type) (m : ℕ), Function.Surjective (rq q G m)) ∧
    ∀ (G : Type) (m : ℕ) (z : Ch ℤ G m), rq q G m z = 0 ↔ ∃ w, z = q • w

def TorsStab : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ m n n' : ℕ, 2 * m + 4 ≤ n → n ≤ n' →
    Finite (AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m)) ∧
      Nat.card (AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m)) = tc L n m

structure IsPrimH {R B : Type} [CommRing R] [AddCommGroup B] {m : ℕ} (φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B) : Prop where
  stab : ∀ n n' (h : n ≤ n') x, φ n' ((grpHMap (stab R n n' h) m).hom x) = φ n x
  psi : ∀ d n x, φ (d * n) ((grpHMap (psi R d n) m).hom x) = d • φ n x

def Descend : Prop :=
  ∀ (R : Type) [CommRing R] (q k : ℕ) (B : Type) [AddCommGroup B] [Module (ZMod q) B]
    (Φ : ∀ n : ℕ, Ch (ZMod q) (GL (Fin n) R) (k + 1) →ₗ[ZMod q] B), IsPrimFam Φ →
      ∃ φ : ∀ n : ℕ, grpH (GL (Fin n) R) (k + 1) →+ B, IsPrimH φ ∧
        ∀ n (z : Ch ℤ (GL (Fin n) R) (k + 1)), Cyc z → ∃ x, φ n x = Φ n (rq q _ (k + 1) z)

def ZVal : Prop :=
  ∀ (R B : Type) [CommRing R] [AddCommGroup B] (m l ν : ℕ) (hl : 0 < l), (∀ b : B, l ^ ν • b = 0) →
    ∀ φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B, IsPrimH φ → ∀ n t : ℕ, ∃ u : ℤ, ∀ x : grpH (GL (Fin n) R) m,
      l ^ t • φ n x = φ (lev l n t) (u • zSeq R hl x t)

def RankCount : Prop :=
  ∀ (H B : Type) [AddCommGroup H] [AddCommGroup B] (q r : ℕ), 0 < q → (∀ b : B, q • b = 0) →
    Finite (AddCommGroup.torsion H) → ∀ (J : Submodule ℤ H), Module.rank ℤ J ≤ r → ∀ (f : H →+ B) (S : Finset B),
      (∀ s ∈ S, ∃ x ∈ J, s = f x) → S.card ≤ q ^ r * Nat.card (AddCommGroup.torsion H)

def Bock : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (G : Type) [Group G] (k : ℕ),
    ∃ β : LinearMap.ker (bd (ZMod q) G k) →+ AddCommGroup.torsion (grpH G k),
      ∀ y, β y = 0 → ∃ z : Ch ℤ G (k + 1), Cyc z ∧ rq q G (k + 1) z = y.1

def FibCount : Prop :=
  ∀ (Y T B : Type) [AddCommGroup Y] [AddCommGroup T] [AddCommGroup B] [Finite T] (β : Y →+ T) (g : Y →+ B) (c : ℕ),
    (∀ S : Finset B, (∀ s ∈ S, ∃ y, β y = 0 ∧ s = g y) → S.card ≤ c) →
      ∀ S : Finset B, (∀ s ∈ S, ∃ y, s = g y) → S.card ≤ c * Nat.card T

end UpperTheory.V.ZK.Up

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RqFacts
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

theorem UpperTheory.V.ZK.Up.rqFacts : UpperTheory.V.ZK.Up.RqFacts := by
  intro q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G _ m z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | single g a =>
      ext i
      simp only [bd, rq, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
        Finsupp.linearCombination_single, Finsupp.smul_apply, Finsupp.add_apply,
        Finsupp.finsetSum_apply, Finsupp.mapRange_apply, smul_eq_mul]
      push_cast
      unfold Finsupp.single
      split_ifs <;> simp [Pi.single_apply, apply_ite]
  · intro G H _ _ f m z
    simp only [cm, rq, Finsupp.lmapDomain_apply, Finsupp.mapRange.addMonoidHom_apply]
    exact Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => by simp)
  · intro G m y
    refine ⟨Finsupp.mapRange (fun x : ZMod q => (x.cast : ℤ)) (by simp) y, ?_⟩
    ext i
    simp [rq]
  · intro G m z
    constructor
    · intro h
      have hd : ∀ i, (q : ℤ) ∣ z i := by
        intro i
        have := DFunLike.congr_fun h i
        simpa [rq, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
      refine ⟨Finsupp.mapRange (fun x : ℤ => x / q) (by simp) z, ?_⟩
      ext i
      simp [Int.mul_ediv_cancel' (hd i)]
    · rintro ⟨w, rfl⟩
      ext i
      simp [rq]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Bridge
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

private theorem d_eq (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : Ch A G (k + 1)) :
    (groupHomology.inhomogeneousChains (Rep.trivial A G A)).d (k + 1) k z = bd A G k z := by
  rw [groupHomology.inhomogeneousChains.d_def]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | single g c =>
    rw [groupHomology.inhomogeneousChains.d_single]
    simp [bd, Finsupp.linearCombination_single, Finset.smul_sum, smul_smul, mul_comm c]

private theorem i_inj (A G : Type) [CommRing A] [Group G] (k : ℕ) :
    Function.Injective (groupHomology.iCycles (Rep.trivial A G A) k) :=
  (ModuleCat.mono_iff_injective (groupHomology.iCycles (Rep.trivial A G A) k)).1 inferInstance

private noncomputable def mk (A G : Type) [CommRing A] [Group G] (k : ℕ) :
    LinearMap.ker (bd A G k) →ₗ[A] groupHomology.cycles (Rep.trivial A G A) (k + 1) where
  toFun z := groupHomology.cyclesMk (k + 1) k (by simp) z.1 ((d_eq A G k z.1).trans z.2)
  map_add' a b := i_inj A G _ (by rw [map_add (f := _), groupHomology.iCycles_mk, groupHomology.iCycles_mk, groupHomology.iCycles_mk]; rfl)
  map_smul' c a := i_inj A G _ (by rw [map_smul, groupHomology.iCycles_mk, groupHomology.iCycles_mk]; rfl)

private theorem i_mk (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : LinearMap.ker (bd A G k)) :
    groupHomology.iCycles (Rep.trivial A G A) (k + 1) (mk A G k z) = z.1 := by
  simp only [_root_.mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact groupHomology.iCycles_mk _ _ _

private theorem pi_zero (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : LinearMap.ker (bd A G k)) :
    groupHomology.π (Rep.trivial A G A) (k + 1) (mk A G k z) = 0 ↔ Bd z.1 := by
  let K := groupHomology.inhomogeneousChains (Rep.trivial A G A)
  have hex : (ShortComplex.mk (K.toCycles (k + 2) (k + 1)) (K.homologyπ (k + 1))
      (K.toCycles_comp_homologyπ _ _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (k + 2) (k + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hti : ∀ y, groupHomology.iCycles (Rep.trivial A G A) (k + 1) (K.toCycles (k + 2) (k + 1) y) =
      bd A G (k + 1) y := by
    intro y
    rw [← d_eq A G (k + 1) y, ← K.toCycles_i (k + 2) (k + 1)]
    rfl
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hex _ h
    refine ⟨y, ?_⟩
    have := congrArg (groupHomology.iCycles (Rep.trivial A G A) (k + 1)) hy
    rw [i_mk] at this
    simpa [hti] using this
  · rintro ⟨y, hy⟩
    have hm : mk A G k z = K.toCycles (k + 2) (k + 1) y := by
      apply i_inj
      rw [i_mk, hti, hy]
    rw [hm]
    exact congrArg (fun f => f y) (congrArg ModuleCat.Hom.hom (K.toCycles_comp_homologyπ (k + 2) (k + 1)))

theorem UpperTheory.V.ZK.Up.bridge : UpperTheory.V.ZK.Up.Bridge := by
  intro k
  refine ⟨fun G _ => ((groupHomology.π (Rep.trivial ℤ G ℤ) (k + 1)).hom ∘ₗ mk ℤ G k).toAddMonoidHom,
    ?_, ?_, ?_⟩
  · intro G _ x
    refine groupHomology_induction_on x ?_
    intro c
    have hc : groupHomology.iCycles (Rep.trivial ℤ G ℤ) (k + 1) c ∈ LinearMap.ker (bd ℤ G k) := by
      rw [LinearMap.mem_ker, ← d_eq]
      exact congrArg (fun g => g.hom c)
        ((groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).iCycles_d (k + 1) k)
    refine ⟨⟨_, hc⟩, ?_⟩
    have hm : mk ℤ G k ⟨_, hc⟩ = c := i_inj ℤ G _ (by rw [i_mk])
    simp [hm]
  · intro G _ z
    exact pi_zero ℤ G k z
  · intro G H _ _ f z z' hz
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply, grpHMap]
    rw [groupHomology.π_map_apply]
    congr 1
    apply i_inj
    have h1 := congrArg (fun g => g.hom (mk ℤ G k z))
      (HomologicalComplex.cyclesMap_i (groupHomology.chainsMap f (trivHom f)) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [i_mk, hz]
    erw [h1, i_mk]
    induction (z : Ch ℤ G (k + 1)) using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | single g a =>
      rw [groupHomology.chainsMap_f_single]
      simp only [cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Descend
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

theorem UpperTheory.V.ZK.Up.descend : UpperTheory.V.ZK.Up.Descend := by
  intro R _ q k B _ _ Φ hΦ
  obtain ⟨cls, hcls⟩ := bridge k
  have hrq := rqFacts q
  have hsc := sChain ℤ
  let g : (n : ℕ) → ↥(bd ℤ (GL (Fin n) R) k).ker →+ B := fun n =>
    ((Φ n).toAddMonoidHom.comp (rq q (GL (Fin n) R) (k + 1))).comp
      (bd ℤ (GL (Fin n) R) k).ker.subtype.toAddMonoidHom
  have hg : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      g n z = Φ n (rq q (GL (Fin n) R) (k + 1) z) := fun _ _ => rfl
  have hker : ∀ n, (cls (GL (Fin n) R)).ker ≤ (g n).ker := by
    intro n z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    rw [hcls.zero _ z] at hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
    rw [hg]
    apply hΦ.bdry
    refine LinearMap.mem_range.mpr ⟨rq q _ (k + 1 + 1) w, ?_⟩
    rw [hrq.1 _ (k + 1) w, hw]
  let φ : (n : ℕ) → ↑(grpH (GL (Fin n) R) (k + 1)) →+ B := fun n =>
    (cls (GL (Fin n) R)).liftOfRightInverse (Function.surjInv (hcls.surj _))
      (Function.rightInverse_surjInv _) ⟨g n, hker n⟩
  have hφ : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      φ n (cls (GL (Fin n) R) z) = Φ n (rq q (GL (Fin n) R) (k + 1) z) := fun n z =>
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z
  have hcyc : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      Cyc (rq q (GL (Fin n) R) (k + 1) (z : Ch ℤ (GL (Fin n) R) (k + 1))) := by
    intro n z
    show bd (ZMod q) _ k _ = 0
    rw [hrq.1, LinearMap.mem_ker.mp z.2, map_zero]
  have hnat : ∀ n n' (f : GL (Fin n) R →* GL (Fin n') R) (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      ∃ z' : ↥(bd ℤ (GL (Fin n') R) k).ker,
        (z' : Ch ℤ (GL (Fin n') R) (k + 1)) = cm ℤ f (k + 1) z := by
    intro n n' f z
    refine ⟨⟨cm ℤ f (k + 1) z, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker, hsc.2.1, LinearMap.mem_ker.mp z.2, map_zero]
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · intro n n' h x
    obtain ⟨z, rfl⟩ := hcls.surj _ x
    obtain ⟨z', hz'⟩ := hnat n n' (stab R n n' h) z
    rw [← hcls.nat _ _ _ z z' hz', hφ, hφ, hz', ← hrq.2.1]
    exact hΦ.stab n n' h _ (hcyc n z)
  · intro d n x
    obtain ⟨z, rfl⟩ := hcls.surj _ x
    obtain ⟨z', hz'⟩ := hnat n (d * n) (psi R d n) z
    rw [← hcls.nat _ _ _ z z' hz', hφ, hφ, hz', ← hrq.2.1, hΦ.psi d n _ (hcyc n z),
      Nat.cast_smul_eq_nsmul]
  · intro n z hz
    exact ⟨cls _ ⟨z, hz⟩, hφ n ⟨z, hz⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.BockAbs
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem bock_abs {C2 C1 C0 D2 D1 H : Type} [AddCommGroup C2] [AddCommGroup C1] [AddCommGroup C0]
    [AddCommGroup D2] [AddCommGroup D1] [AddCommGroup H] {A : Type} [CommRing A] [Module A D2] [Module A D1]
    (q : ℕ) (hq : 0 < q) (d1 : C2 →ₗ[ℤ] C1) (d0 : C1 →ₗ[ℤ] C0) (e : D2 →ₗ[A] D1) (r2 : C2 →+ D2) (r1 : C1 →+ D1)
    (hdd : ∀ z, d0 (d1 z) = 0) (hc : ∀ z, e (r2 z) = r1 (d1 z)) (hs : Function.Surjective r2)
    (h2 : ∀ z, r2 z = 0 ↔ ∃ w, z = q • w) (h1 : ∀ z, r1 z = 0 ↔ ∃ w, z = q • w)
    (t1 : ∀ w : C1, q • w = 0 → w = 0) (t0 : ∀ w : C0, q • w = 0 → w = 0)
    (cls : LinearMap.ker d0 →+ H) (hz : ∀ z, cls z = 0 ↔ z.1 ∈ LinearMap.range d1) :
    ∃ β : LinearMap.ker e →+ AddCommGroup.torsion H, ∀ y, β y = 0 → ∃ z : C2, d1 z = 0 ∧ r2 z = y.1 := by
  classical
  have hlift : ∀ y : LinearMap.ker e, ∃ x : C2, ∃ w : C1, r2 x = y.1 ∧ d1 x = q • w := by
    intro y
    obtain ⟨x, hx⟩ := hs y.1
    have h0 : r1 (d1 x) = 0 := by
      rw [← hc, hx]
      exact y.2
    obtain ⟨w, hw⟩ := (h1 _).1 h0
    exact ⟨x, w, hx, hw⟩
  have hker : ∀ (x : C2) (w : C1), d1 x = q • w → d0 w = 0 := by
    intro x w h
    apply t0
    rw [← map_nsmul, ← h, hdd]
  have hwd : ∀ (x x' : C2) (w w' : C1) (hw0 : d0 w = 0) (hw0' : d0 w' = 0), r2 x = r2 x' →
      d1 x = q • w → d1 x' = q • w' →
      cls ⟨w, LinearMap.mem_ker.2 hw0⟩ = cls ⟨w', LinearMap.mem_ker.2 hw0'⟩ := by
    intro x x' w w' hw0 hw0' hr h h'
    obtain ⟨u, hu⟩ := (h2 (x' - x)).1 (by rw [map_sub, hr, sub_self])
    have hd : d1 u ∈ LinearMap.ker d0 := LinearMap.mem_ker.2 (hdd u)
    have heq : w' = w + d1 u := by
      apply sub_eq_zero.1
      apply t1
      rw [smul_sub, smul_add, ← h, ← h', ← map_nsmul, ← hu, map_sub]
      abel
    have hsum : (⟨w', LinearMap.mem_ker.2 hw0'⟩ : LinearMap.ker d0) = ⟨w, LinearMap.mem_ker.2 hw0⟩ + ⟨d1 u, hd⟩ :=
      Subtype.ext heq
    rw [hsum, map_add (f := _), (hz ⟨d1 u, hd⟩).2 ⟨u, rfl⟩, add_zero]
  choose X W hXr hXd using hlift
  have hW0 : ∀ y, d0 (W y) = 0 := fun y => hker _ _ (hXd y)
  let f : LinearMap.ker e → H := fun y => cls ⟨W y, LinearMap.mem_ker.2 (hW0 y)⟩
  have htor : ∀ y, f y ∈ AddCommGroup.torsion H := by
    intro y
    refine (AddCommGroup.mem_torsion _).2 (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, hq, ?_⟩)
    have hm : q • (⟨W y, LinearMap.mem_ker.2 (hW0 y)⟩ : LinearMap.ker d0) = ⟨d1 (X y), by
        rw [LinearMap.mem_ker, hdd]⟩ := Subtype.ext (hXd y).symm
    show q • cls _ = 0
    rw [← map_nsmul, hm, (hz _).2 ⟨X y, rfl⟩]
  refine ⟨{ toFun := fun y => ⟨f y, htor y⟩, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply Subtype.ext
    show f 0 = 0
    have h00 := hwd (X 0) 0 (W 0) 0 (hW0 0) (map_zero _) (by simp [hXr]) (hXd 0) (by simp)
    exact h00.trans (map_zero cls)
  · intro a b
    apply Subtype.ext
    show f (a + b) = f a + f b
    have hab := hwd (X (a + b)) (X a + X b) (W (a + b)) (W a + W b) (hW0 _)
      (by rw [map_add (f := _), hW0, hW0, add_zero]) (by rw [map_add (f := _), hXr, hXr, hXr]; rfl)
      (hXd _) (by rw [map_add (f := _), hXd, hXd, smul_add])
    exact hab.trans (map_add cls ⟨W a, LinearMap.mem_ker.2 (hW0 a)⟩ ⟨W b, LinearMap.mem_ker.2 (hW0 b)⟩)
  · intro y hy
    have hy' : f y = 0 := congrArg Subtype.val hy
    obtain ⟨v, hv⟩ := (hz _).1 hy'
    refine ⟨X y - q • v, ?_, ?_⟩
    · rw [map_sub, map_nsmul, hv, hXd, sub_self]
    · rw [map_sub, hXr, (h2 _).2 ⟨v, rfl⟩, sub_zero]

private theorem ch_tf (q : ℕ) (hq : 0 < q) (G : Type) (m : ℕ) (w : Ch ℤ G m) (h : q • w = 0) : w = 0 := by
  refine Finsupp.ext fun a => ?_
  have h' := congrArg (fun v => v a) h
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, nsmul_eq_mul] at h'
  rcases mul_eq_zero.1 h' with h0 | h0
  · have : q = 0 := by exact_mod_cast h0
    omega
  · rw [h0]
    rfl

private theorem bd_zero (G : Type) [Group G] (z : Ch ℤ G 1) : bd ℤ G 0 z = 0 := by
  have hv : (fun g : Fin (0 + 1) → G => (fun₀ | (fun i : Fin 0 => g i.succ) => (1 : ℤ)) +
      ∑ j : Fin (0 + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
        (fun₀ | j.contractNth (fun x1 x2 : G => x1 * x2) g => (1 : ℤ))) = 0 := by
    funext g
    rw [Fin.sum_univ_one, Subsingleton.elim (Fin.contractNth (0 : Fin (0 + 1)) (fun x1 x2 : G => x1 * x2) g)
      (fun i : Fin 0 => g i.succ)]
    simp
  simp only [bd, hv, Finsupp.linearCombination_zero, LinearMap.zero_apply]

theorem UpperTheory.V.ZK.Up.bock :
    UpperTheory.V.ZK.Up.Bock := by
  intro q hq G _ k
  obtain ⟨f1, -, f3, f4⟩ := rqFacts q
  cases k with
  | zero =>
    refine ⟨0, fun y _ => ?_⟩
    obtain ⟨z, hz⟩ := f3 G 1 y.1
    exact ⟨z, bd_zero G z, hz⟩
  | succ k =>
    obtain ⟨cls, hcls⟩ := bridge k
    exact bock_abs q hq (bd ℤ G (k + 1)) (bd ℤ G k) (bd (ZMod q) G (k + 1)) (rq q G (k + 2)) (rq q G (k + 1))
      ((sChain ℤ).1 G k) (f1 G (k + 1)) (f3 G _) (f4 G _) (f4 G _) (ch_tf q hq G _) (ch_tf q hq G _) (cls G)
      (hcls.zero G)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.TorsStab
open CategoryTheory NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.Up.card_tors_eq {M N : Type} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    Nat.card (AddCommGroup.torsion M) = Nat.card (AddCommGroup.torsion N) := by
  have key : ∀ x : M, x ∈ AddCommGroup.torsion M ↔ e x ∈ AddCommGroup.torsion N := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  exact Nat.card_congr (e.toEquiv.subtypeEquiv key)

theorem UpperTheory.V.ZK.Up.torsStab :
    UpperTheory.V.ZK.Up.TorsStab := by
  intro L _ _ hL m n n' hn hnn'
  haveI := hL
  have hiso : ∀ k, 2 * m + 4 ≤ k → IsIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m) :=
    fun k hk => PositivityTheory.v8.KStability.kStability (𝓞 L) 2 (dedekindSR (𝓞 L)) m k (by omega)
  have he : Nonempty ((grpH (GL (Fin n) (𝓞 L)) m : Type) ≃+ (grpH (GL (Fin n') (𝓞 L)) m : Type)) := by
    induction n', hnn' using Nat.le_induction with
    | base => exact ⟨AddEquiv.refl _⟩
    | succ k hk ih =>
      obtain ⟨e⟩ := ih
      haveI := hiso k (by omega)
      exact ⟨e.trans (asIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m)).toLinearEquiv.toAddEquiv⟩
  obtain ⟨e⟩ := he
  have key : ∀ x, x ∈ AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type) ↔
      e x ∈ AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m : Type) := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  have hfin : Finite (AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type)) :=
    (UpperTheory.V.KT.tors_le L n m).1
  refine ⟨Finite.of_equiv _ (e.toEquiv.subtypeEquiv key), ?_⟩
  rw [← UpperTheory.V.ZK.Up.card_tors_eq e]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCountAlt
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem rankCount_gen (M : Type) [AddCommGroup M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.rank ℤ M ≤ r) :
    ∃ (s : ℕ) (v : Fin s → M), s ≤ r ∧ ∀ m : M, ∃ c : Fin s → ℤ,
      m - ∑ i, c i • v i ∈ Submodule.torsion ℤ M := by
  classical
  haveI : Module.Free ℤ (M ⧸ Submodule.torsion ℤ M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (M ⧸ Submodule.torsion ℤ M)
  have hs : Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) ≤ r := by
    have h1 : (Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) : Cardinal) ≤ r := by
      rw [Module.finrank_eq_rank]
      exact (rank_quotient_le _).trans hr
    exact_mod_cast h1
  have hv : ∀ i, ∃ v : M, (Submodule.torsion ℤ M).mkQ v = b i :=
    fun i => Submodule.mkQ_surjective _ (b i)
  choose v hv using hv
  refine ⟨_, v, hs, fun m => ⟨fun i => b.repr ((Submodule.torsion ℤ M).mkQ m) i, ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
  simp only [map_smul, hv]
  rw [b.sum_repr, sub_self]

private theorem zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero {B : Type} [AddCommGroup B] (q : ℕ) (hq : 0 < q) (w : B)
    (hw : q • w = 0) (a : ℤ) : a • w = ((a % (q : ℤ)).toNat) • w := by
  have h0 : 0 ≤ a % (q : ℤ) := Int.emod_nonneg _ (by omega)
  rw [← natCast_zsmul, Int.toNat_of_nonneg h0]
  have ha : a = a % (q : ℤ) + (a / (q : ℤ)) * (q : ℤ) := by
    rw [Int.emod_def]
    ring
  conv_lhs => rw [ha]
  rw [add_smul, mul_smul, natCast_zsmul, hw, smul_zero, add_zero]

theorem UpperTheory.V.ZK.Up.rankCount :
    UpperTheory.V.ZK.Up.RankCount := by
  intro H B _ _ q r hq hB hT J hJ f S hS
  classical
  haveI := Fintype.ofFinite (AddCommGroup.torsion H)
  choose! x hxJ hx using hS
  let J' : Submodule ℤ H := Submodule.span ℤ ((fun b => x b) '' (S : Set B))
  haveI : Module.Finite ℤ J' := Module.Finite.span_of_finite _ ((S.finite_toSet).image _)
  have hJJ : J' ≤ J := Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact hxJ b hb)
  have hJ' : Module.rank ℤ J' ≤ r := (Submodule.rank_mono hJJ).trans hJ
  obtain ⟨s, v, hsr, hv⟩ := rankCount_gen J' r hJ'
  let Φ : (Fin s → Fin q) × AddCommGroup.torsion H → B :=
    fun p => ∑ i, ((p.1 i : ℕ)) • f ((v i : J') : H) + f p.2
  have hsub : S ⊆ Finset.univ.image Φ := by
    intro b hb
    have hm : x b ∈ J' := Submodule.subset_span ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := hv ⟨x b, hm⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hc
    have ht : (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) ∈ AddCommGroup.torsion H := by
      rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(a : ℤ), nonZeroDivisors.coe_ne_zero a, ?_⟩
      have := congrArg (fun y : J' => (y : H)) ha
      simpa [Submonoid.smul_def] using this
    refine Finset.mem_image.2 ⟨(fun i => ⟨(c i % (q : ℤ)).toNat, ?_⟩, ⟨_, ht⟩), Finset.mem_univ _, ?_⟩
    · have h1 : c i % (q : ℤ) < q := Int.emod_lt_of_pos _ (by omega)
      have h2 : 0 ≤ c i % (q : ℤ) := Int.emod_nonneg _ (by omega)
      omega
    · simp only [Φ]
      have hxb : x b = (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) + ∑ i, c i • ((v i : J') : H) := by
        simp
      conv_rhs => rw [hx b hb, hxb]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero q hq _ (hB _)]
  calc S.card ≤ (Finset.univ.image Φ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin s → Fin q) × AddCommGroup.torsion H)).card := Finset.card_image_le
    _ = q ^ s * Nat.card (AddCommGroup.torsion H) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          Nat.card_eq_fintype_card]
    _ ≤ q ^ r * Nat.card (AddCommGroup.torsion H) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hsr)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.PhiZSeq
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.Up.phi_zSeq {R B : Type} [CommRing R] [AddCommGroup B] {m l : ℕ} (hl : 0 < l)
    (φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B) (hφ : IsPrimH φ) (n t : ℕ) :
    ∃ c : ℤ, ∀ x : grpH (GL (Fin n) R) m,
      φ (lev l n t) (zSeq R hl x t) = ((l : ℤ) ^ t * (1 - l * c)) • φ n x := by
  induction t with
  | zero => exact ⟨0, fun x => by simp only [pow_zero, mul_zero, sub_zero, mul_one, one_smul]; rfl⟩
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (l : ℤ) ^ t - l * c * (l : ℤ) ^ t, fun x => ?_⟩
    have h : φ (lev l n (t + 1)) (zSeq R hl x (t + 1)) =
        φ (l * lev l n t) ((grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) -
          l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom
            (zSeq R hl x t)) := rfl
    rw [h, map_sub, map_nsmul, hφ.psi, hφ.stab, hc, ← natCast_zsmul, ← natCast_zsmul, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring

theorem UpperTheory.V.ZK.Up.zVal :
    UpperTheory.V.ZK.Up.ZVal := by
  intro R B _ _ m l ν hl hB φ hφ n t
  obtain ⟨c, hc⟩ := UpperTheory.V.ZK.Up.phi_zSeq hl φ hφ n t
  refine ⟨∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i, fun x => ?_⟩
  have hg : (∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i) * ((l : ℤ) ^ t * (1 - l * c)) =
      (l : ℤ) ^ t - ((l : ℤ) ^ t * c ^ ν) * ((l ^ ν : ℕ) : ℤ) := by
    have := geom_sum_mul_neg ((l : ℤ) * c) ν
    push_cast
    rw [mul_left_comm, this, mul_pow]
    ring
  rw [map_zsmul, hc, smul_smul, hg, sub_smul, mul_smul _ ((l ^ ν : ℕ) : ℤ), natCast_zsmul, hB, smul_zero, sub_zero,
    ← natCast_zsmul, Nat.cast_pow]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.FibCount
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

theorem UpperTheory.V.ZK.Up.fibCount : UpperTheory.V.ZK.Up.FibCount := by
  intro Y T B _ _ _ _ β g c hc S hS
  classical
  choose! y hy using hS
  have := Fintype.ofFinite T
  calc S.card ≤ c * (S.image (fun s => β (y s))).card := by
        apply Finset.card_le_mul_card_image
        intro t _
        rcases (S.filter (fun s => β (y s) = t)).eq_empty_or_nonempty with hF | ⟨s₀, hs₀⟩
        · rw [hF]
          simp
        · rw [← Finset.card_image_of_injective _ (sub_left_injective (b := s₀))]
          apply hc
          intro u hu
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
          have hs' := Finset.mem_filter.1 hs
          have hs₀' := Finset.mem_filter.1 hs₀
          refine ⟨y s - y s₀, by rw [map_sub, hs'.2, hs₀'.2, sub_self], ?_⟩
          rw [map_sub, ← hy s hs'.1, ← hy s₀ hs₀'.1]
    _ ≤ c * Nat.card T := by
        apply Nat.mul_le_mul_left
        rw [Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
end

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.rankCount_mod (hR : RankCount) (H B : Type) [AddCommGroup H] [inst : Module ℤ H]
    [AddCommGroup B] (q r : ℕ) (hq : 0 < q) (hB : ∀ b : B, q • b = 0) (hH : Finite (AddCommGroup.torsion H)) (X : Set H)
    (hX : Module.rank ℤ (Submodule.span ℤ X) ≤ r) (f : H →+ B) (S : Finset B)
    (hS : ∀ s ∈ S, ∃ x ∈ X, ∃ u : ℤ, s = f (SMul.smul (self := (AddCommGroup.toIntModule H).toSMul) u x)) :
    S.card ≤ q ^ r * Nat.card (AddCommGroup.torsion H) := by
  obtain rfl : inst = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  refine hR H B q r hq hB hH _ hX f S fun s hs => ?_
  obtain ⟨x, hx, u, e⟩ := hS s hs
  exact ⟨u • x, Submodule.smul_mem _ u (Submodule.subset_span hx), e⟩

private theorem UpperTheory.V.ZK.selmer_upper_bound_of_inputs (hS : TorsStab) (hD : Descend) (hZ : ZVal) (hR : RankCount) (hB : Bock)
    (hF : FibCount) : UpperTheory.V.ZK.SUpperOf := by
  intro hC hO L _ _ hL k hk hr l ν hl B _ _ Φ hΦ S hSm
  classical
  have hl0 : 0 < l := hl.out.pos
  have hq : 0 < l ^ ν := pow_pos hl0 ν
  have hqB : ∀ b : B, l ^ ν • b = 0 := fun b => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ ν)), ZMod.natCast_self, zero_smul]
  obtain ⟨φ, hφ, hφΦ⟩ := hD (𝓞 L) (l ^ ν) k B Φ hΦ
  choose! nn hnn using hSm
  obtain ⟨n, hn0, hnS⟩ : ∃ n, 2 * (k + 1) + 4 ≤ n ∧ ∀ s ∈ S, nn s ≤ n :=
    ⟨max (2 * (k + 1) + 4) (S.sup nn), le_max_left _ _, fun s hs => le_max_of_le_right (Finset.le_sup hs)⟩
  obtain ⟨β, hβ⟩ := hB (l ^ ν) hq (GL (Fin n) (𝓞 L)) k
  obtain ⟨hfin, hcard⟩ := hS L hL k (2 * (k + 1) + 4) n (by omega) hn0
  have hlev : ∀ t, n ≤ lev l n t := fun t => by
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (Nat.le_mul_of_pos_left _ hl0)
  obtain ⟨hfin', hcard'⟩ := hS L hL (k + 1) (2 * (k + 1) + 4) (lev l n k) le_rfl (hn0.trans (hlev k))
  obtain ⟨u, hu⟩ := hZ (𝓞 L) B (k + 1) l ν hl0 hqB φ hφ n k
  let g : LinearMap.ker (bd (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) k) →+ B :=
    (nsmulAddMonoidHom (l ^ k)).comp
      ((Φ n).toAddMonoidHom.comp (LinearMap.ker (bd (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) k)).subtype.toAddMonoidHom)
  have hg : ∀ y, g y = l ^ k • Φ n y.1 := fun y => rfl
  have key := hF _ _ B β g ((l ^ ν) ^ InfinitePlace.nrComplexPlaces L * tc L (2 * (k + 1) + 4) (k + 1)) ?_ S ?_
  · rw [hcard] at key
    exact key
  · intro T hT
    rw [← hcard']
    refine rankCount_mod hR _ B (l ^ ν) _ hq hqB hfin' _ (hO L hL k hk hr l hl0 n hn0) (φ (lev l n k)) T fun s hs => ?_
    obtain ⟨y, hy, rfl⟩ := hT s hs
    obtain ⟨z, hz, hzy⟩ := hβ y hy
    obtain ⟨x, hx⟩ := hφΦ n z hz
    refine ⟨zSeq (𝓞 L) hl0 x k, ⟨x, rfl⟩, u, ?_⟩
    rw [hg, ← hzy, ← hx, hu]
    rfl
  · intro s hs
    obtain ⟨y, hy, e⟩ := hnn s hs
    refine ⟨⟨cm _ (stab (𝓞 L) (nn s) n (hnS s hs)) (k + 1) y, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, (hC _).2.1, show bd _ _ k y = 0 from hy, map_zero]
    · rw [hg, hΦ.stab _ _ _ _ hy]
      exact e

theorem UpperTheory.V.ZK.sUpperOf :
    UpperTheory.V.ZK.SUpperOf :=
  selmer_upper_bound_of_inputs torsStab descend zVal rankCount bock fibCount

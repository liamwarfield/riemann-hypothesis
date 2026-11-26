module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.GlobalTwistedTraceBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PRankOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.SeenTrA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PMinIdem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.HeckeComp
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F
open PositivityTheory.RgTw (Mat G)

private theorem hecke_comp {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {φ : G → G} (hc : Continuous φ)
    (hi : ∀ g, φ (φ g) = g) (hm : ∀ a b, φ (a * b) = φ a * φ b) (hK : ∀ k ∈ K, φ k ∈ K) {h : G → ℂ}
    (hh : IsHecke K h) : IsHecke K (fun g => h (φ g)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · let e : G ≃ₜ G :=
      { toFun := φ, invFun := φ, left_inv := hi, right_inv := hi,
        continuous_toFun := hc, continuous_invFun := hc }
    exact hh.1.comp_homeomorph e
  · simp only [hm]
    exact hh.2 _ (hK k hk) _

private theorem core {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (hS : LvShift) (ρ : Representation ℂ G V) (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (u : G) (hu : ∀ x, x ∈ K ↔ u * x * u⁻¹ ∈ K) (θ : G → G)
    (hθc : Continuous θ) (hθi : ∀ g, θ (θ g) = g) (hθm : ∀ a b, θ (a * b) = θ a * θ b) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hθu : θ u = u⁻¹) (Y : Submodule ℂ V) (hY : Y ≤ fixed ρ K) (r : (G → ℂ) → Module.End ℂ Y)
    (hact : ∀ h, IsHecke K h → ∀ y : Y, (r h y : V) = Lv ρ K h y)
    (A : Module.End ℂ Y) (hAA : A * A = 1)
    (hA : ∀ h, IsHecke K h → A * r h = r (fun g => h (θ g)) * A) :
    (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) = 1 ∧
    (∀ h, IsHecke K h → (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * r h =
      r (fun g => h (u * θ g * u⁻¹)) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A)) ∧
    ∀ h, IsHecke K h → IsHecke K (fun g => h (g * u⁻¹)) ∧
      r (fun g => h (g * u⁻¹)) = r h * r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) := by
  have h0 : IsHecke K (0 : G → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have Sh := hS G V ρ K ho hc
  have hI : IsHecke K ((K : Set G).indicator 1) := (Sh u hu 0 h0).2.2.1
  have hu' : ∀ x, x ∈ K ↔ u⁻¹ * x * u⁻¹⁻¹ ∈ K := fun x => by
    rw [hu (u⁻¹ * x * u⁻¹⁻¹)]
    simp [mul_assoc]

  have a1 : ∀ v : G, (∀ x, x ∈ K ↔ v * x * v⁻¹ ∈ K) → ∀ y : Y,
      (r (fun g => (K : Set G).indicator 1 (v⁻¹ * g)) y : V) = ρ v y := fun v hv y => by
    obtain ⟨-, hl, -, -⟩ := Sh v hv _ hI
    obtain ⟨-, -, e1, e2⟩ := (Sh v hv _ hI).2.2.2 y (hY y.2)
    rw [hact _ hl, e1, e2]
  set Ru := r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) with hRu
  set Ru' := r (fun g => (K : Set G).indicator 1 (u * g)) with hRu'
  have b1 : ∀ y : Y, (Ru y : V) = ρ u y := a1 u hu
  have b2 : ∀ y : Y, (Ru' y : V) = ρ u⁻¹ y := fun y => by
    have := a1 u⁻¹ hu' y
    simpa only [inv_inv] using this
  have hRR : Ru * Ru' = 1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show (Ru (Ru' y) : V) = y
    rw [b1, b2, ← Module.End.mul_apply, ← map_mul]
    simp
  have hAR : A * Ru = Ru' * A := by
    rw [hRu, hA _ (Sh u hu _ hI).2.1, hRu']
    congr 2
    funext g
    have e : u⁻¹ * θ g = θ (u * g) := by rw [hθm, hθu]
    have m : θ (u * g) ∈ K ↔ u * g ∈ K :=
      ⟨fun h => by simpa only [hθi] using hθK _ h, hθK _⟩
    rw [e]
    by_cases c : u * g ∈ K
    · rw [Set.indicator_of_mem (by exact_mod_cast m.2 c), Set.indicator_of_mem (by exact_mod_cast c)]
      rfl
    · rw [Set.indicator_of_notMem (by exact_mod_cast fun d => c (m.1 d)), Set.indicator_of_notMem (by exact_mod_cast c)]
  have hθu' : θ u⁻¹ = u := by rw [← hθu, hθi]
  refine ⟨?_, fun h hh => ?_, fun h hh => ?_⟩
  · calc (Ru * A) * (Ru * A) = Ru * (A * Ru) * A := by simp only [mul_assoc]
      _ = (Ru * Ru') * (A * A) := by rw [hAR]; simp only [mul_assoc]
      _ = 1 := by rw [hRR, hAA, one_mul]
  · have hf : IsHecke K (fun g => h (θ g)) := hecke_comp hθc hθi hθm hθK hh
    have hf' : IsHecke K (fun g => h (u * θ g * u⁻¹)) := by
      refine hecke_comp (φ := fun g => u * θ g * u⁻¹) (by fun_prop) (fun g => ?_) (fun a b => ?_) (fun k hk => ?_) hh
      · show u * θ (u * θ g * u⁻¹) * u⁻¹ = g
        rw [hθm, hθm, hθu, hθu', hθi]
        group
      · show u * θ (a * b) * u⁻¹ = u * θ a * u⁻¹ * (u * θ b * u⁻¹)
        rw [hθm]
        group
      · exact (hu _).1 (hθK k hk)
    have e : Ru * r (fun g => h (θ g)) = r (fun g => h (u * θ g * u⁻¹)) * Ru := by
      refine LinearMap.ext fun y => Subtype.ext ?_
      show (Ru (r (fun g => h (θ g)) y) : V) = (r (fun g => h (u * θ g * u⁻¹)) (Ru y) : V)
      obtain ⟨p1, p2, -⟩ := Sh u hu _ hf
      obtain ⟨q1, q2, -⟩ := Sh u hu _ hf'
      obtain ⟨-, -, e1, -⟩ := (Sh u hu _ hf).2.2.2 y (hY y.2)
      obtain ⟨-, e2, -, -⟩ := (Sh u hu _ hf').2.2.2 y (hY y.2)
      have ef : (fun g => h (θ (u⁻¹ * g))) = fun g => h (u * θ (g * u⁻¹) * u⁻¹) := by
        funext g
        rw [hθm, hθm, hθu']
        congr 1
        group
      rw [b1, hact _ hf, hact _ hf', b1, ← e1, ← e2, ef]
    calc (Ru * A) * r h = Ru * (A * r h) := by rw [mul_assoc]
      _ = (Ru * r (fun g => h (θ g))) * A := by rw [hA h hh, mul_assoc]
      _ = r (fun g => h (u * θ g * u⁻¹)) * (Ru * A) := by rw [e, mul_assoc]
  · obtain ⟨p1, -⟩ := Sh u hu h hh
    refine ⟨p1, LinearMap.ext fun y => Subtype.ext ?_⟩
    show (r (fun g => h (g * u⁻¹)) y : V) = (r h (Ru y) : V)
    obtain ⟨-, e2, -, -⟩ := (Sh u hu h hh).2.2.2 y (hY y.2)
    rw [hact _ p1, hact _ hh, b1, e2]

theorem UpperTheory.V.Z.Mult.Pi.toYdA :
    SlotBasic → LevTop → TranslF → HeckeSum → LvShift → UpperTheory.V.Z.Mult.Pi.ToYdA := by
  intro hSl hLT hTF hHS hLS E _ _ _ n S Z N hS hZ hG π u hu
  obtain ⟨hO, hC, -, hNm⟩ := hLT E n S Z N hS hZ hG
  obtain ⟨t1, t2, κ, hκ, t3⟩ := hTF E n u hu
  have hinv := (hSl E n S hS).1
  have hcont := (hSl E n S hS).2.1
  have hthe : ∀ g, thetaF E n g = (ratF E n u)⁻¹ * thF E n g * ratF E n u := by
    intro g
    rw [t1 g]
    group
  have hnorm : ∀ x, x ∈ Lev S N ↔ ratF E n u * x * (ratF E n u)⁻¹ ∈ Lev S N := by
    intro x
    rw [t3 x]
    refine ⟨hNm κ hκ x, fun hx => ?_⟩
    have := hNm κ⁻¹ ((Kf E n).inv_mem hκ) _ hx
    simpa [mul_assoc] using this
  have hθK : ∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N := by
    intro k hk
    refine (hnorm _).2 ?_
    have e : ratF E n u * thetaF E n k * (ratF E n u)⁻¹ = thF E n k := (t1 k).symm
    rw [e]
    exact (hLT E n S Z N hS hZ hG).2.2.1 k hk
  refine ⟨hθK, ?_⟩
  intro μf hμ Y ρ A hYπ hfd hne hfix hAct hsim hAA hAθ
  have hθm : ∀ a b, thetaF E n (a * b) = thetaF E n a * thetaF E n b := by
    intro a b
    simp only [hthe, map_mul]
    group
  have hθi : ∀ g, thetaF E n (thetaF E n g) = g := by
    intro g
    simp only [hthe, map_mul, map_inv, t2, hinv]
    group
  have hθu : thetaF E n (ratF E n u) = (ratF E n u)⁻¹ := by
    rw [hthe, t2]
    group
  have hθc : Continuous (thetaF E n) := by
    have : thetaF E n = fun g => (ratF E n u)⁻¹ * thF E n g * ratF E n u := funext hthe
    rw [this]
    exact (continuous_const.mul hcont).mul continuous_const
  have hv : (μf (Lev S N : Set (GF E n))).toReal ≠ 0 := by
    haveI := hμ
    exact (ENNReal.toReal_pos (hO.measure_pos μf ⟨1, (Lev S N).one_mem⟩).ne' hC.measure_lt_top.ne).ne'
  obtain ⟨v, hvdef⟩ : ∃ v : ℂ, v = (((μf (Lev S N : Set (GF E n))).toReal : ℝ) : ℂ) := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact_mod_cast hv
  have toF : ∀ {h : GF E n → ℂ}, IsHecke (Lev S N) h → IsHeckeF (Lev S N) h := fun hh =>
    ⟨hh.1, fun k₁ h₁ k₂ h₂ g => by rw [(hh.2 _ h₂ _).2, (hh.2 _ h₁ _).1]⟩
  have toH : ∀ {h : GF E n → ℂ}, IsHeckeF (Lev S N) h → IsHecke (Lev S N) h := fun hh =>
    ⟨hh.1, fun k hk x => ⟨by simpa using hh.2 k hk 1 (Lev S N).one_mem x,
      by simpa using hh.2 1 (Lev S N).one_mem k hk x⟩⟩
  have hY : Y ≤ fixed (finRep E n) (Lev S N) := fun y hy k => by
    simpa using hfix y hy k k.2
  have hact : ∀ h, IsHecke (Lev S N) h → ∀ y : Y,
      (((v⁻¹ • ρ h : Module.End ℂ Y) y : Y) : Sm E n) = Lv (finRep E n) (Lev S N) h y := by
    intro h hh y
    have e : ((ρ h y : Y) : Sm E n) = v • Lv (finRep E n) (Lev S N) h y := by
      refine Subtype.ext ?_
      have e1 := hAct h (toF hh) y
      have e2 := hHS E n (Lev S N) hO hC μf hμ h hh y (hY y.2)
      rw [e1, e2, hvdef]
      rfl
    show ((v⁻¹ • (ρ h y) : Y) : Sm E n) = _
    rw [Submodule.coe_smul, e, inv_smul_smul₀ hv0]
  obtain ⟨c1, c2, c3⟩ := core hLS (finRep E n) (Lev S N) hO hC (ratF E n u) hnorm (thetaF E n) hθc hθi hθm hθK hθu
    Y hY (fun h => v⁻¹ • ρ h) hact A hAA (fun h hh => by
      rw [mul_smul_comm, smul_mul_assoc, hAθ h (toF hh)])
  refine ⟨⟨Y, fun h => v⁻¹ • ρ h, _, hYπ, hfd, hne, hY, hact, ?_, c1, ?_⟩, v, hvdef, fun h hh =>
    ⟨toF (c3 h hh).1, ?_⟩⟩
  · intro W hW
    refine hsim W fun h hh y hy => ?_
    exact (W.smul_mem_iff (inv_ne_zero hv0)).1 (hW h (toH hh) y hy)
  · intro h hh
    have e : (fun g => h (thF E n g)) = fun g => h (ratF E n u * thetaF E n g * (ratF E n u)⁻¹) :=
      funext fun g => by rw [t1 g]
    show _ * _ = (v⁻¹ • ρ (fun g => h (thF E n g))) * _
    rw [e]
    exact c2 h hh
  · have e2 : v⁻¹ • ρ (fun g => h (g * (ratF E n u)⁻¹)) = (v⁻¹ • ρ h) *
        (v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) := (c3 h hh).2
    have key : ρ (fun g => h (g * (ratF E n u)⁻¹)) * A = v • ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [← mul_assoc, ← e2, smul_mul_assoc, smul_inv_smul₀ hv0]
    have tr : LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ Y ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [key, LinearMap.map_smul, smul_eq_mul]
    exact tr
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.AbsGlobA
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

noncomputable section

namespace UpperTheory.V.Z.Mult.Pi.AbsoluteGlobal

section Pure

variable {ι : Type} {U : Type} [AddCommGroup U] [Module ℂ U]

private theorem capp {a b : Module.End ℂ U} (h : Commute a b) (x : U) : a (b x) = b (a x) :=
  LinearMap.congr_fun h.eq x

private def fixS (e : ι → Module.End ℂ U) (s : Finset ι) : Submodule ℂ U where
  carrier := {x | ∀ i ∈ s, e i x = x}
  add_mem' {x y} hx hy i hi := by rw [map_add (f := _), hx i hi, hy i hi]
  zero_mem' i _ := map_zero _
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi]

private theorem mem_fixS {e : ι → Module.End ℂ U} {s : Finset ι} {x : U} : x ∈ fixS e s ↔ ∀ i ∈ s, e i x = x := Iff.rfl

private theorem compress [Nontrivial U] (A : ι → Subalgebra ℂ (Module.End ℂ U)) (e : ι → Module.End ℂ U)
    (Rs : Set (Module.End ℂ U)) (hee : ∀ i x, e i (e i x) = e i x) (hc : ∀ i j, Commute (e i) (e j))
    (heA : ∀ i j, i ≠ j → ∀ a ∈ A j, Commute (e i) a) (heR : ∀ i, ∀ r ∈ Rs, Commute (e i) r)
    (hAA : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (hAR : ∀ i, ∀ a ∈ A i, ∀ r ∈ Rs, Commute a r)
    (hs : ∀ W : Submodule ℂ U, (∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) → (∀ r ∈ Rs, ∀ x ∈ W, r x ∈ W) → W = ⊥ ∨ W = ⊤)
    (he0 : ∀ i, ∃ x, e i x ≠ 0) (s : Finset ι) :
    (∃ y ∈ fixS e s, y ≠ 0) ∧ ∀ W ≤ fixS e s, (∀ r ∈ Rs, ∀ x ∈ W, r x ∈ W) →
      (∀ i ∈ s, ∀ a ∈ A i, ∀ x ∈ W, e i (a x) ∈ W) → (∀ i ∉ s, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) →
      W = ⊥ ∨ W = fixS e s := by
  classical
  have hK : ∀ i (y : U), y ≠ 0 → ∃ a ∈ A i, e i (a y) ≠ 0 := by
    intro i y hy
    let K : Submodule ℂ U :=
      { carrier := {z | ∀ a ∈ A i, e i (a z) = 0}
        add_mem' := fun {x z} hx hz a ha => by rw [map_add (f := _), map_add (f := _), hx a ha, hz a ha, add_zero]
        zero_mem' := fun a _ => by rw [map_zero, map_zero]
        smul_mem' := fun c x hx a ha => by rw [map_smul, map_smul, hx a ha, smul_zero] }
    have hKs := hs K (fun j b hb x hx a ha => by
        by_cases hij : i = j
        · subst hij
          exact hx (a * b) (mul_mem ha hb)
        · rw [capp (hAA i j hij a ha b hb), capp (heA i j hij b hb), hx a ha, map_zero])
      (fun r hr x hx a ha => by rw [capp (hAR i a ha r hr), capp (heR i r hr), hx a ha, map_zero])
    by_contra hcon
    push Not at hcon
    rcases hKs with h | h
    · have : y ∈ K := hcon
      rw [h] at this
      exact hy this
    · obtain ⟨x, hx⟩ := he0 i
      have : x ∈ K := h ▸ Submodule.mem_top
      exact hx (this 1 (one_mem _))
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨y, hy⟩ := exists_ne (0 : U)
    refine ⟨⟨y, fun i hi => absurd hi (Finset.notMem_empty i), hy⟩, fun W _ hR _ hA => ?_⟩
    rcases hs W (fun i => hA i (Finset.notMem_empty i)) hR with h | h
    · exact Or.inl h
    · refine Or.inr (h.trans (Submodule.eq_top_iff'.2 fun x i hi => absurd hi (Finset.notMem_empty i)).symm)
  | insert i s hi ih =>
    obtain ⟨⟨y, hy, hy0⟩, ih⟩ := ih
    have hne : ∀ j ∈ s, j ≠ i := fun j hj h => hi (h ▸ hj)
    refine ⟨?_, fun W hW hR h1 h2 => ?_⟩
    · obtain ⟨a, ha, h0⟩ := hK i y hy0
      refine ⟨_, fun j hj => ?_, h0⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hee _ _
      · rw [capp (hc j i), capp (heA j i (hne j hj) a ha), hy j hj]
    · let M : Submodule ℂ U := Submodule.span ℂ {z | ∃ a ∈ A i, ∃ w ∈ W, a w = z}
      have gen : ∀ a ∈ A i, ∀ w ∈ W, a w ∈ M := fun a ha w hw => Submodule.subset_span ⟨a, ha, w, hw, rfl⟩
      have ind : ∀ (f : Module.End ℂ U) (N : Submodule ℂ U), (∀ a ∈ A i, ∀ w ∈ W, f (a w) ∈ N) → ∀ x ∈ M, f x ∈ N := by
        intro f N h x hx
        have : M ≤ N.comap f := Submodule.span_le.2 (by
          rintro _ ⟨a, ha, w, hw, rfl⟩
          exact h a ha w hw)
        exact this hx
      have hM := ih M (fun x hx => ind 1 (fixS e s) (fun a ha w hw j hj => by
          show e j (a w) = a w
          rw [capp (heA j i (hne j hj) a ha), hW hw j (Finset.mem_insert_of_mem hj)]) x hx)
        (fun r hr => ind r M fun a ha w hw => by
          rw [← capp (hAR i a ha r hr)]
          exact gen a ha _ (hR r hr w hw))
        (fun j hj b hb => ind (e j * b) M fun a ha w hw => by
          show e j (b (a w)) ∈ M
          rw [capp (hAA j i (hne j hj) b hb a ha), capp (heA j i (hne j hj) a ha)]
          exact gen a ha _ (h1 j (Finset.mem_insert_of_mem hj) b hb w hw))
        (fun j hj b hb => ind b M fun a ha w hw => by
          by_cases hji : j = i
          · subst hji
            exact gen (b * a) (mul_mem hb ha) w hw
          · rw [capp (hAA j i hji b hb a ha)]
            exact gen a ha _ (h2 j (by simp [hji, hj]) b hb w hw))
      rcases hM with h | h
      · refine Or.inl (eq_bot_iff.2 fun w hw => ?_)
        rw [← h]
        exact gen 1 (one_mem _) w hw
      · refine Or.inr (le_antisymm hW fun z hz => ?_)
        have hzM : z ∈ M := h ▸ fun j hj => hz j (Finset.mem_insert_of_mem hj)
        rw [← hz i (Finset.mem_insert_self i s)]
        exact ind (e i) W (fun a ha w hw => h1 i (Finset.mem_insert_self i s) a ha w hw) z hzM

variable {F : Submodule ℂ U}

private theorem trOn_map (S : Submodule ℂ F) {f : Module.End ℂ U} {g : Module.End ℂ F}
    (h : ∀ x, (g x : U) = f x) : trOn (S.map F.subtype) f = trOn S g := by
  have hiff : (∀ x ∈ S.map F.subtype, f x ∈ S.map F.subtype) ↔ ∀ x ∈ S, g x ∈ S := by
    constructor
    · intro H x hx
      obtain ⟨z, hz, hzx⟩ := H x ⟨x, hx, rfl⟩
      have : z = g x := Subtype.ext (hzx.trans (h x).symm)
      exact this ▸ hz
    · rintro H _ ⟨x, hx, rfl⟩
      exact ⟨g x, H x hx, h x⟩
  unfold trOn
  by_cases H : ∀ x ∈ S, g x ∈ S
  · rw [dite_eq_left H, dite_eq_left (hiff.2 H),
      ← LinearMap.trace_conj' _ (Submodule.equivMapOfInjective F.subtype F.injective_subtype S).symm]
    congr 1
    ext x
    simp only [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have : (f.restrict (hiff.2 H)) (Submodule.equivMapOfInjective F.subtype F.injective_subtype S x) =
        Submodule.equivMapOfInjective F.subtype F.injective_subtype S (g.restrict H x) := Subtype.ext (h x).symm
    rw [this, LinearEquiv.symm_apply_apply]
  · rw [dite_eq_right H, dite_eq_right fun H' => H (hiff.1 H')]

private theorem trOn_self {f : Module.End ℂ U} {g : Module.End ℂ F}
    (h : ∀ x, (g x : U) = f x) : trOn F f = LinearMap.trace ℂ F g := by
  have H : ∀ x ∈ F, f x ∈ F := fun x hx => h ⟨x, hx⟩ ▸ (g ⟨x, hx⟩).2
  unfold trOn
  rw [dite_eq_left H]
  congr 1
  ext x
  exact (h x).symm


variable (F) in
private def resAlg (B : Subalgebra ℂ (Module.End ℂ U)) : Subalgebra ℂ (Module.End ℂ F) where
  carrier := {g | ∃ b ∈ B, ∀ x, (g x : U) = b x}
  mul_mem' := by
    rintro g g' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    exact ⟨b * b', mul_mem hb hb', fun x => by simp [h, h']⟩
  add_mem' := by
    rintro g g' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    exact ⟨b + b', add_mem hb hb', fun x => by simp [h, h']⟩
  algebraMap_mem' c := ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ _, fun x => by simp [Module.algebraMap_end_apply]⟩

private theorem list_res {κ : Type} (a : κ → Module.End ℂ U) (g : κ → Module.End ℂ F) (h : ∀ o x, (g o x : U) = a o x)
    (l : List κ) (x : F) : ((l.map g).prod x : U) = (l.map a).prod x := by
  induction l with
  | nil => simp
  | cons o l ih => simp [h, ih]

private theorem descend (hMF : MultiFac) {κ : Type} [Fintype κ] [FiniteDimensional ℂ F] (hF : F ≠ ⊥)
    (B : κ → Subalgebra ℂ (Module.End ℂ U)) (Θ : Module.End ℂ U)
    (hB : ∀ i j, i ≠ j → ∀ a ∈ B i, ∀ b ∈ B j, Commute a b) (hΘ : Θ * Θ = 1) (hΘF : ∀ x ∈ F, Θ x ∈ F)
    (hΘB : ∀ i, ∀ a ∈ B i, Θ * a * Θ ∈ B i)
    (hs : ∀ W ≤ F, (∀ i, ∀ a ∈ B i, (∀ x ∈ F, a x ∈ F) → ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = F) :
    ∃ (S : κ → Submodule ℂ U) (s : ℂ), ‖s‖ = 1 ∧
      (∀ i, S i ≤ F ∧ S i ≠ ⊥ ∧ (∀ a ∈ B i, (∀ x ∈ F, a x ∈ F) → ∀ x ∈ S i, a x ∈ S i) ∧ (∀ x ∈ S i, Θ x ∈ S i) ∧
        ∀ W ≤ S i, (∀ a ∈ B i, (∀ x ∈ F, a x ∈ F) → ∀ x ∈ W, a x ∈ W) → W = ⊥ ∨ W = S i) ∧
      ∀ a : κ → Module.End ℂ U, (∀ i, a i ∈ B i) → (∀ i, ∀ x ∈ F, a i x ∈ F) →
        trOn F (((Finset.univ : Finset κ).toList.map a).prod * Θ) = s * ∏ i, trOn (S i) (a i * Θ) := by
  haveI : Nontrivial F := Submodule.nontrivial_iff_ne_bot.2 hF
  have hinj := Submodule.map_injective_of_injective F.injective_subtype
  obtain ⟨Fi, s, hs1, hFi, htr⟩ := hMF κ F (fun i => resAlg F (B i)) (Θ.restrict hΘF)
    (by
      rintro i j hij g ⟨b, hb, h⟩ g' ⟨b', hb', h'⟩
      ext x
      simp [h, h', capp (hB i j hij b hb b' hb')])
    (by
      intro W hW
      rcases hs (W.map F.subtype) (Submodule.map_subtype_le F W) (by
        rintro i a ha haF _ ⟨x, hx, rfl⟩
        exact ⟨_, hW i (a.restrict haF) ⟨a, ha, fun _ => rfl⟩ x hx, rfl⟩) with h | h
      · exact Or.inl (hinj (h.trans (Submodule.map_bot _).symm))
      · exact Or.inr (hinj (h.trans (Submodule.map_subtype_top F).symm)))
    (by
      ext x
      exact LinearMap.congr_fun hΘ x)
    (by
      rintro i g ⟨b, hb, h⟩
      exact ⟨_, hΘB i b hb, fun x => by simp [h]⟩)
  refine ⟨fun i => (Fi i).map F.subtype, s, by rcases hs1 with rfl | rfl <;> norm_num, fun i => ?_, fun a ha haF => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hFi i
    refine ⟨Submodule.map_subtype_le F _, fun h => h1 (hinj (h.trans (Submodule.map_bot _).symm)), ?_, ?_, ?_⟩
    · rintro a ha haF _ ⟨x, hx, rfl⟩
      exact ⟨_, h2 (a.restrict haF) ⟨a, ha, fun _ => rfl⟩ x hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, h3 x hx, rfl⟩
    · intro W hW hst
      have hWF : W ≤ F := hW.trans (Submodule.map_subtype_le F _)
      have hmc : (W.comap F.subtype).map F.subtype = W := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hWF]
      rcases h4 (W.comap F.subtype) (fun x hx => by
          obtain ⟨z, hz, hzx⟩ := hW hx
          exact (Subtype.ext hzx : z = x) ▸ hz)
        (by
          rintro g ⟨b, hb, h⟩ x hx
          show (g x : U) ∈ W
          rw [h]
          exact hst b hb (fun y hy => h ⟨y, hy⟩ ▸ (g ⟨y, hy⟩).2) _ hx) with h | h
      · exact Or.inl (by rw [← hmc, h, Submodule.map_bot])
      · exact Or.inr (by rw [← hmc, h])
  · have := htr (fun i => (a i).restrict (haF i)) fun i => ⟨a i, ha i, fun _ => rfl⟩
    rw [trOn_self (g := ((Finset.univ : Finset κ).toList.map fun i => (a i).restrict (haF i)).prod * Θ.restrict hΘF)
      (fun x => list_res a _ (fun _ _ => rfl) _ _), this]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (trOn_map _ fun _ => rfl).symm

private theorem prod_option [Fintype ι] (a : Option ι → Module.End ℂ U) (h : ∀ i j, i ≠ j → Commute (a i) (a j)) :
    ((Finset.univ : Finset (Option ι)).toList.map a).prod =
      ((Finset.univ : Finset ι).toList.map fun i => a (some i)).prod * a none := by
  have hp : (Finset.univ : Finset (Option ι)).toList.Perm ((Finset.univ : Finset ι).toList.map some ++ [none]) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).2 fun o => ?_
    · rw [List.nodup_append]
      refine ⟨(Finset.nodup_toList _).map (Option.some_injective _), List.nodup_singleton _, ?_⟩
      simp
    · cases o <;> simp
  rw [(hp.map a).prod_eq' (List.pairwise_map.2 ((Finset.nodup_toList _).imp fun hij => h _ _ hij))]
  simp [List.map_map, Function.comp_def]

end Pure

section Gen

variable {U : Type} [AddCommGroup U] [Module ℂ U]

private theorem adjoin_comm {s t : Set (Module.End ℂ U)} (h : ∀ a ∈ s, ∀ b ∈ t, Commute a b) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∀ b ∈ Algebra.adjoin ℂ t, Commute a b := fun a ha b hb =>
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun y hy =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun x hx => (h x hx y hy).symm).symm

private theorem adjoin_stab {s : Set (Module.End ℂ U)} {N : Submodule ℂ U} (h : ∀ a ∈ s, ∀ x ∈ N, a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∀ x ∈ N, a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem z hz => exact h z hz
  | algebraMap c => exact fun x hx => N.smul_mem c hx
  | add u v _ _ hu hv => exact fun x hx => N.add_mem (hu x hx) (hv x hx)
  | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)

private theorem adjoin_conj {s : Set (Module.End ℂ U)} {Θ : Module.End ℂ U} (hΘ : Θ * Θ = 1)
    (h : ∀ a ∈ s, ∃ b ∈ s, Θ * a = b * Θ) : ∀ a ∈ Algebra.adjoin ℂ s, Θ * a * Θ ∈ Algebra.adjoin ℂ s := by
  have key : ∀ a ∈ Algebra.adjoin ℂ s, ∃ b ∈ Algebra.adjoin ℂ s, Θ * a = b * Θ := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem z hz => exact (h z hz).imp fun b hb => ⟨Algebra.subset_adjoin hb.1, hb.2⟩
    | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, (Algebra.commutes c Θ).symm⟩
    | add u v _ _ hu hv =>
      obtain ⟨⟨b, hb, e⟩, b', hb', e'⟩ := And.intro hu hv
      exact ⟨b + b', add_mem hb hb', by rw [mul_add, add_mul, e, e']⟩
    | mul u v _ _ hu hv =>
      obtain ⟨⟨b, hb, e⟩, b', hb', e'⟩ := And.intro hu hv
      exact ⟨b * b', mul_mem hb hb', by rw [← mul_assoc, e, mul_assoc, e', mul_assoc]⟩
  intro a ha
  obtain ⟨b, hb, e⟩ := key a ha
  rwa [e, mul_assoc, hΘ, mul_one]

private def orb (A : Subalgebra ℂ (Module.End ℂ U)) (x : U) : Submodule ℂ U :=
  (Subalgebra.toSubmodule A).map (LinearMap.applyₗ x)

private theorem mem_orb {A : Subalgebra ℂ (Module.End ℂ U)} {x y : U} : y ∈ orb A x ↔ ∃ a ∈ A, a x = y := Iff.rfl

private theorem list_fix {ι : Type} (P : ι → Module.End ℂ U) (e : Module.End ℂ U) (h : ∀ j, Commute e (P j)) (i : ι)
    (hi : ∀ x, e (P i x) = P i x) (l : List ι) (hl : i ∈ l) (x : U) : e ((l.map P).prod x) = (l.map P).prod x := by
  induction l with
  | nil => simp at hl
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rcases List.mem_cons.1 hl with rfl | hl
    · exact hi _
    · rw [capp (h j), ih hl]

end Gen

section Adj

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

private theorem pair_adj {E1 E2 : Fin n → Fin n → Module.End ℂ U} (h : IsPair E1 E2) (a b : Fin n) :
    (∀ x y : U, ⟪E1 a b x, y⟫_ℂ = ⟪x, E2 b a y⟫_ℂ) ∧ ∀ x y : U, ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ := by
  have hK : ∀ x y : U, ⟪E1 a b x, y⟫_ℂ + ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ + ⟪x, E2 b a y⟫_ℂ := fun x y => by
    simpa [kF, inner_add_left, inner_add_right] using h.unitK a b x y
  have hP : ∀ x y : U, ⟪E1 a b x, y⟫_ℂ - ⟪E2 a b x, y⟫_ℂ = -(⟪x, E1 b a y⟫_ℂ - ⟪x, E2 b a y⟫_ℂ) := fun x y => by
    simpa only [pF, LinearMap.sub_apply, inner_sub_left, inner_sub_right] using h.unitP a b x y
  exact ⟨fun x y => by linear_combination (hK x y + hP x y) / 2, fun x y => by linear_combination (hK x y - hP x y) / 2⟩

private theorem iso_adj {f g : Module.End ℂ U} (h : ∀ x y : U, ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ) (hfg : f * g = 1) (x y : U) :
    ⟪f x, y⟫_ℂ = ⟪x, g y⟫_ℂ := by
  rw [← h x (g y), ← Module.End.mul_apply, hfg, Module.End.one_apply]

end Adj

end UpperTheory.V.Z.Mult.Pi.AbsoluteGlobal

open UpperTheory.V.Z.Mult.Pi.AbsoluteGlobal in
theorem UpperTheory.V.Z.Mult.Pi.absGlobA :
    MultiFac → LieStab → ProjEx → AvgFacts → OnePlace → UpperTheory.V.Z.Mult.Pi.AbsGlobA := by
  intro hMF hLS hPE hAF hOP n ι _ lam hlam E T hT _ _ ν _ hν U _ _ E1 E2 σ Θ P J R hloc havg hEE hσσ hRc hRa hRΘ hΘ
    hsimp hnt hfd hne
  classical
  choose e he using fun i => hPE n U (σ i) (hloc i).isK (E i)
  have hP := fun i => hAF n ν U (σ i) (hloc i).isK (E i) (T i) (P i) (hT i).1 (havg i)
  have hce : ∀ i {x}, AdjComm (σ i) x → Commute (e i) x := fun i x hx => (he i).2.2.2.2.1 x hx
  have hcP : ∀ i {x}, AdjComm (σ i) x → Commute (P i) x := fun i x hx => (hP i).2.2.1 x hx
  have hiso : ∀ i x, x ∈ isoSp (σ i) (E i) ↔ e i x = x :=
    fun i x => ⟨(he i).2.2.1 x, fun h => h ▸ (he i).2.1 x⟩

  let G : ι → Set (Module.End ℂ U) := fun i => {x | ∃ a b, x = E1 i a b ∨ x = E2 i a b}
  let Gs : Option ι → Set (Module.End ℂ U) := fun o => o.elim (Set.range R) fun i => G i ∪ {e i, P i}
  have aσ : ∀ i j, i ≠ j → ∀ k, AdjComm (σ i) (σ j k) := fun i j hij k =>
    ⟨σ j k⁻¹, iso_adj ((hloc j).isK.iso k) (by rw [← map_mul, mul_inv_cancel, map_one]),
      fun k' => ⟨hσσ j i hij.symm _ _, hσσ j i hij.symm _ _⟩⟩
  have aΘ : ∀ i, AdjComm (σ i) Θ := fun i =>
    ⟨Θ, iso_adj (hloc i).Aiso hΘ, fun k => ⟨(hloc i).Aσ k, (hloc i).Aσ k⟩⟩
  have aG : ∀ i j, i ≠ j → ∀ x ∈ G j, AdjComm (σ i) x := by
    rintro i j hij _ ⟨a, b, rfl | rfl⟩
    · exact ⟨_, (pair_adj (hloc j).pair a b).1,
        fun k => ⟨((hEE j i hij.symm a b).2 k).1, ((hEE j i hij.symm b a).2 k).2⟩⟩
    · exact ⟨_, (pair_adj (hloc j).pair a b).2,
        fun k => ⟨((hEE j i hij.symm a b).2 k).2, ((hEE j i hij.symm b a).2 k).1⟩⟩
  have aR : ∀ i j, AdjComm (σ i) (R j) := fun i j =>
    (hRa j).elim fun j' h => ⟨R j', h, fun k => ⟨(hRc j i).2 k, (hRc j' i).2 k⟩⟩
  have ae : ∀ i j, AdjComm (σ i) (e j) := by
    intro i j
    have : ∀ k, e j * σ i k = σ i k * e j := by
      by_cases h : j = i
      · subst h
        exact (he j).2.2.2.1
      · exact fun k => hce j (aσ j i h k)
    exact ⟨e j, (he j).1, fun k => ⟨this k, this k⟩⟩
  have aP : ∀ i j, AdjComm (σ i) (P j) := by
    intro i j
    by_cases h : j = i
    · subst h
      exact (hP j).2.1
    · obtain ⟨P', h1, h2⟩ := (hP j).2.2.2.2
      exact ⟨P', h1, fun k => ⟨hcP j (aσ j i h k), h2 _ (aσ j i h k)⟩⟩
  have aGs : ∀ i j, i ≠ j → ∀ x ∈ Gs (some j), AdjComm (σ i) x := by
    rintro i j hij x (hx | rfl | rfl)
    exacts [aG i j hij x hx, ae i j, aP i j]
  have cGG : ∀ i j, i ≠ j → ∀ x ∈ G i, ∀ y ∈ G j, Commute x y := by
    rintro i j hij _ ⟨a, b, rfl | rfl⟩ _ ⟨c, d, rfl | rfl⟩
    exacts [((hEE i j hij a b).1 c d).1, ((hEE i j hij a b).1 c d).2.1, ((hEE j i hij.symm c d).1 a b).2.1.symm,
      ((hEE i j hij a b).1 c d).2.2]
  have cGR : ∀ i, ∀ x ∈ Gs (some i), ∀ y ∈ Set.range R, Commute x y := by
    rintro i _ (⟨a, b, rfl | rfl⟩ | rfl | rfl) _ ⟨j, rfl⟩
    exacts [((hRc j i).1 a b).1.symm, ((hRc j i).1 a b).2.symm, hce i (aR i j), hcP i (aR i j)]
  have cGs : ∀ o o', o ≠ o' → ∀ x ∈ Gs o, ∀ y ∈ Gs o', Commute x y := by
    rintro (_ | i) (_ | j) h x hx y hy
    · exact absurd rfl h
    · exact (cGR j y hy x hx).symm
    · exact cGR i x hx y hy
    · have hij : i ≠ j := fun h' => h (congrArg some h')
      rcases hx with hx | rfl | rfl
      · rcases hy with hy | rfl | rfl
        exacts [cGG i j hij x hx y hy, (hce j (aG j i hij.symm x hx)).symm, (hcP j (aG j i hij.symm x hx)).symm]
      · exact hce i (aGs i j hij y hy)
      · exact hcP i (aGs i j hij y hy)
  let B : Option ι → Subalgebra ℂ (Module.End ℂ U) := fun o => Algebra.adjoin ℂ (Gs o)
  have cB : ∀ o o', o ≠ o' → ∀ x ∈ B o, ∀ y ∈ B o', Commute x y := fun o o' h => adjoin_comm (cGs o o' h)
  have hAB : ∀ i, alg (E1 i) (E2 i) ≤ B (some i) := fun i => Algebra.adjoin_mono Set.subset_union_left
  have heB : ∀ i, e i ∈ B (some i) := fun i => Algebra.subset_adjoin (Or.inr (Or.inl rfl))
  have hPB : ∀ i, P i ∈ B (some i) := fun i => Algebra.subset_adjoin (Or.inr (Or.inr rfl))
  have hRB : ∀ j, R j ∈ B none := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have cij : ∀ i j, i ≠ j → ∀ x ∈ B (some i), ∀ y ∈ B (some j), Commute x y :=
    fun i j h => cB _ _ fun h' => h (Option.some.inj h')
  set F : Submodule ℂ U := ⨅ i, isoSp (σ i) (E i) with hFdef
  have hF : ∀ x, x ∈ F ↔ ∀ i, e i x = x := fun x => by simp only [hFdef, Submodule.mem_iInf, hiso]
  have hFfix : fixS e Finset.univ = F := Submodule.ext fun x => by simp [mem_fixS, hF]
  have keep : ∀ a : Module.End ℂ U, (∀ i, Commute (e i) a) → ∀ x ∈ F, a x ∈ F := fun a ha x hx =>
    (hF _).2 fun i => by rw [capp (ha i), (hF x).1 hx i]
  have hee : ∀ i x, e i (e i x) = e i x := fun i x => (hiso i _).1 ((he i).2.1 x)
  have keepE : ∀ i, ∀ a ∈ B (some i), ∀ x ∈ F, (e i * a) x ∈ F := fun i a ha x hx => (hF _).2 fun j => by
    by_cases h : j = i
    · subst h
      exact hee _ _
    · rw [capp (cij j i h _ (heB j) _ (mul_mem (heB i) ha)), (hF x).1 hx j]
  have keepR : ∀ j, ∀ x ∈ F, R j x ∈ F := fun j => keep _ fun i => hce i (aR i j)
  have keepP : ∀ j, ∀ x ∈ F, P j x ∈ F := fun j => keep _ fun i => hce i (aP i j)
  obtain ⟨⟨y, hy, hy0⟩, hFs⟩ := compress (fun i => alg (E1 i) (E2 i)) e (Set.range R) hee (fun i j => hce i (ae i j))
    (fun i j h a ha => cij i j h _ (heB i) _ (hAB j ha))
    (by rintro i _ ⟨j, rfl⟩; exact hce i (aR i j))
    (fun i j h a ha b hb => cij i j h _ (hAB i ha) _ (hAB j hb))
    (by rintro i a ha _ ⟨j, rfl⟩; exact cB _ _ (Option.some_ne_none i) _ (hAB i ha) _ (hRB j))
    (fun W h1 h2 => hsimp W (fun i a b x hx =>
      ⟨h1 i _ (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) x hx, h1 i _ (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩) x hx⟩)
      fun j => h2 _ ⟨j, rfl⟩)
    (fun i => by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
      exact ⟨x, by rwa [(hiso i x).1 hx]⟩) Finset.univ
  rw [hFfix] at hy hFs
  have hΘ2 : ∀ i a b, Θ * E2 i a b = E1 i a b * Θ := fun i a b => by
    have h := (hloc i).AE a b
    calc Θ * E2 i a b = Θ * (E2 i a b * Θ) * Θ := by rw [mul_assoc, mul_assoc, hΘ, mul_one]
      _ = E1 i a b * Θ := by rw [← h, ← mul_assoc, hΘ, one_mul]
  obtain ⟨S, s, hs0, hS, htr⟩ := descend (F := F) hMF ((Submodule.ne_bot_iff _).2 ⟨y, hy, hy0⟩) B Θ cB hΘ
    (keep _ fun i => hce i (aΘ i))
    (fun o => adjoin_conj hΘ (by
      rcases o with _ | i
      · rintro _ ⟨j, rfl⟩
        obtain ⟨j', h⟩ := hRΘ j
        exact ⟨_, ⟨j', rfl⟩, h⟩
      · rintro _ (⟨a, b, rfl | rfl⟩ | rfl | rfl)
        · exact ⟨_, Or.inl ⟨a, b, Or.inr rfl⟩, (hloc i).AE a b⟩
        · exact ⟨_, Or.inl ⟨a, b, Or.inl rfl⟩, hΘ2 i a b⟩
        · exact ⟨_, Or.inr (Or.inl rfl), (hce i (aΘ i)).symm⟩
        · exact ⟨_, Or.inr (Or.inr rfl), (hcP i (aΘ i)).symm⟩))
    (fun W hW h => hFs W hW (by rintro _ ⟨j, rfl⟩; exact h none _ (hRB j) (keepR j))
      (fun i _ a ha => h (some i) (e i * a) (mul_mem (heB i) (hAB i ha)) (keepE i a (hAB i ha)))
      fun i hi => absurd (Finset.mem_univ i) hi)

  have horb : ∀ i x, ∀ a ∈ B (some i), a x ∈ orb (alg (E1 i) (E2 i)) x := by
    intro i x a ha
    have hA : ∀ c ∈ alg (E1 i) (E2 i), ∀ z ∈ orb (alg (E1 i) (E2 i)) x, c z ∈ orb (alg (E1 i) (E2 i)) x := by
      rintro c hc _ ⟨b, hb, rfl⟩
      exact mem_orb.2 ⟨c * b, mul_mem hc (show b ∈ alg (E1 i) (E2 i) from hb), rfl⟩
    have hσ := hLS n U (σ i) _ (hloc i).der (orb (alg (E1 i) (E2 i)) x) fun a b =>
      hA _ (add_mem (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩))
    refine adjoin_stab ?_ a ha x (mem_orb.2 ⟨1, one_mem _, rfl⟩)
    rintro c (hc | rfl | rfl)
    exacts [hA c (Algebra.subset_adjoin hc), (he i).2.2.2.2.2 _ hσ, (hP i).2.2.2.1 _ hσ]
  have hloc2 : ∀ i, ‖trOn (S (some i)) (P i * Θ)‖ = 2 ^ n := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS (some i)
    have := hOP n (lam i) (hlam i) (E i) (T i) (hT i) ν hν U (E1 i) (E2 i) (σ i) Θ (P i) (hloc i) (havg i) (S (some i))
      (Submodule.finiteDimensional_of_le h1) h2 (h1.trans (iInf_le _ i)) h4
      (fun a ha x hx hax => by
        rw [← (hiso i _).1 hax]
        exact h3 (e i * a) (mul_mem (heB i) (hAB i ha)) (keepE i a (hAB i ha)) x hx)
      (fun x hx z hz hx0 => by
        rcases h5 (S (some i) ⊓ orb (alg (E1 i) (E2 i)) x) inf_le_left (by
          rintro a ha haF _ ⟨hw, b, hb, rfl⟩
          exact ⟨h3 a ha haF _ hw, horb i x (a * b) (mul_mem ha (hAB i hb))⟩) with h | h
        · have : x ∈ S (some i) ⊓ orb (alg (E1 i) (E2 i)) x := ⟨hx, mem_orb.2 ⟨1, one_mem _, rfl⟩⟩
          rw [h] at this
          exact absurd this hx0
        · rw [← h] at hz
          exact hz.2)
    rcases this with h | h <;> rw [h] <;> simp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS none
  refine ⟨S none, s * ∏ i, trOn (S (some i)) (P i * Θ), by rw [norm_mul, hs0, one_mul, norm_prod, Finset.prod_congr rfl fun i _ => hloc2 i, Finset.prod_const, Finset.card_univ],
    Submodule.finiteDimensional_of_le h1, h2, fun j => h3 _ (hRB j) (keepR j), h4, fun W hW h => h5 W hW fun a ha _ =>
      adjoin_stab (by rintro _ ⟨j, rfl⟩; exact h j) a ha, fun x => (hF _).2 fun i => ?_, fun j => ?_⟩
  · exact list_fix P (e i) (fun j => hce i (aP i j)) i (fun x => (hiso i _).1 ((hP i).1 x)) _ (by simp) x
  · have ha : ∀ o : Option ι, o.elim (R j) P ∈ B o := by
      rintro (_ | i)
      exacts [hRB j, hPB i]
    have := htr (fun o => o.elim (R j) P) ha (by
      rintro (_ | i)
      exacts [keepR j, keepP i])
    rw [prod_option _ fun o o' h => cB o o' h _ (ha o) _ (ha o'), Fintype.prod_option] at this
    refine this.trans ?_
    simp only [Option.elim]
    ring
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.OpFormA
noncomputable section

open NumberField MeasureTheory Measure
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (G)

namespace UpperTheory.V.Z.GSp4Splitting

section Iter

variable {X Γ U ι : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [Monoid Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [AddCommGroup U] [Module ℂ U]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem prod_cs {κ : Type} [Fintype κ] (e : κ → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) :
    Continuous (fun y : κ → X => ∏ v, e v (y v)) ∧ HasCompactSupport (fun y : κ → X => ∏ v, e v (y v)) := by
  refine ⟨continuous_finsetProd _ fun v _ => (he v).1.comp (continuous_apply v), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (he v).2.isCompact) fun y hy => ?_
  obtain ⟨v, hv⟩ := not_forall.1 (mt Set.mem_univ_pi.2 hy)
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

private theorem iter_fin (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (m : ℕ) :
    ∀ (s : Fin m → ι) (u : U) (g : Γ),
      ∫ y : Fin m → X, (∏ i, e (s i) (y i)) * Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod) ∂(Measure.pi fun _ => μ) =
        (∏ i, val (s i)) * Φ ((List.ofFn fun i => P (s i)).prod u) g := by
  induction m with
  | zero =>
    intro s u g
    simp [Measure.pi_of_empty (fun _ : Fin 0 => μ)]
  | succ m ih =>
    intro s u g
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hl : Continuous fun y : Fin (m + 1) → X => (List.ofFn fun i => j (s i) (y i)).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun i _ => (hj _).comp (continuous_apply i)
    have hF : Integrable (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) (Measure.pi fun _ => μ) :=
      ((prod_cs (fun i => e (s i)) fun i => he _).1.mul ((hΦ u).comp (continuous_const.mul hl))).integrable_of_hasCompactSupport
        (prod_cs (fun i => e (s i)) fun i => he _).2.mul_right
    rw [← (hmp.symm _).integral_comp']
    refine (integral_prod _ (((hmp.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF)).trans ?_
    have hin : ∀ t : X, ∫ z : Fin m → X, (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) ((MeasurableEquiv.piFinSuccAbove (fun _ => X) 0).symm (t, z))
          ∂(Measure.pi fun _ => μ) = (∏ i : Fin m, val (s i.succ)) *
            (e (s 0) t * Φ ((List.ofFn fun i : Fin m => P (s i.succ)).prod u) (g * j (s 0) t)) := by
      intro t
      have e1 : ∀ z : Fin m → X, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0).symm (t, z) = Fin.cons t z :=
        fun z => Fin.insertNth_zero' t z
      simp only [e1, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
      simp only [← mul_assoc g, mul_assoc (e (s 0) t)]
      rw [integral_const_mul, ih (fun i => s i.succ) u (g * j (s 0) t)]
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall hin)).trans ?_
    rw [integral_const_mul, hloc, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    ring

private theorem iter_list [Fintype ι] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (l : List ι) (hl : l.Nodup) (hm : ∀ v, v ∈ l)
    (u : U) (g : Γ) :
    ∫ y : ι → X, (∏ v, e v (y v)) * Φ u (g * (l.map fun v => j v (y v)).prod) ∂(Measure.pi fun _ => μ) =
      (∏ v, val v) * Φ ((l.map P).prod u) g := by
  classical
  let σ : Fin l.length ≃ ι := List.Nodup.getEquivOfForallMemList l hl hm
  have hσ : ∀ {β : Type} (f : ι → β), (List.ofFn fun i => f (σ i)) = l.map f := fun f => by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => μ) σ
  have key := iter_fin μ e he j hj Φ hΦ val P hloc _ σ u g
  rw [hσ P, Equiv.prod_comp σ val] at key
  rw [← key, ← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ∀ i, MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ y (σ i) = y i := fun i =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) σ y i
  beta_reduce
  rw [← hσ, ← Equiv.prod_comp σ]
  simp only [e1]

end Iter

private theorem prod_single {ι M : Type} [DecidableEq ι] [Monoid M] (y : ι → M) :
    ∀ l : List ι, l.Nodup → ∀ w, (l.map fun v => (Pi.mulSingle v (y v) : ι → M)).prod w = if w ∈ l then y w else 1 := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hl w
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl.2]
    by_cases h : w = a
    · subst h
      simp [hl.1]
    · simp [h]

private theorem split_two {X Y K : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (e : X × Y ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ]
    (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = c * ∫ x, ∫ y, f (e (x, y)) ∂mY ∂mX := by
  let em : X × Y ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  haveI : IsHaarMeasure ((mX.prod mY).map e) := ContinuousMulEquiv.isHaarMeasure_map _ e
  haveI : LocallyCompactSpace K := e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology K := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  have h := isMulLeftInvariant_eq_smul μ ((mX.prod mY).map e)
  have hpos := haarScalarFactor_pos_of_isHaarMeasure μ ((mX.prod mY).map e)
  generalize haarScalarFactor μ ((mX.prod mY).map e) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun f hf hs => ?_⟩
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine (integral_map_equiv em f).trans ?_
  exact integral_prod (fun z => f (e z))
    ((hf.comp e.continuous).integrable_of_hasCompactSupport (hs.comp_homeomorph e.toHomeomorph))

private theorem hecke_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : Γ → ℂ) (hh : ∀ k ∈ K, ∀ g, h (g * k) = h g) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hn : (fun x => g⁻¹ * x) ⁻¹' (K : Set Γ) ∈ nhds g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  refine continuousAt_const.congr (f := fun _ => h g) (Filter.mem_of_superset hn fun x hx => ?_)
  have := hh _ hx g
  simpa using this.symm


open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG in
private def split0 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* PositivityTheory.Rg.BcB.E.H E n 0 where
  toFun p := (splitGA n p, 1)
  invFun g := (splitGA n).symm g.1
  left_inv p := by simp
  right_inv g := Prod.ext (by simp) (Units.ext (Matrix.ext fun i => Fin.elim0 i))
  map_mul' p q := by simp
  continuous_toFun := (splitGA n).continuous.prodMk continuous_const
  continuous_invFun := (splitGA n).symm.continuous.comp continuous_fst

end UpperTheory.V.Z.GSp4Splitting

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH PositivityTheory.Rg.BcB.CG.lc_G PositivityTheory.Rg.BcB.CG.sc_G PositivityTheory.Rg.BcB.CG.lc_GLf
  PositivityTheory.Rg.BcB.CG.sc_GLf PositivityTheory.Rg.BcB.CG.t2_GL_finite_adeles PositivityTheory.Rg.BcB.CG.borelSpaceH in
open PositivityTheory.Rg.BcB.CG in
theorem UpperTheory.V.Z.Mult.Pi.opFormA :
    LocAct → UpperTheory.V.Z.Mult.Pi.OpFormA := by
  intro hL E _ _ _ n _ _ μC _ _ _ μf _ μ _
  classical
  haveI : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μC) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := split_two (split0 E n) μ (Measure.pi fun _ : InfinitePlace E => μC) μf
  refine ⟨c, hc0, fun hn π hθ K hKo hKc hKθ D lam hch _ _ ν _ hν P hP k val T hk h hh ψ u hu x => ?_⟩
  set e : InfinitePlace E → G n → ℂ := fun w => phiOf (lefE n (lam w)) (lefT n (lam w)) (k w) with he
  have hecs : ∀ w, Continuous (e w) ∧ HasCompactSupport (e w) := fun w =>
    PositivityTheory.Rg.BcB.F.F0.phiOf_cs μC _ _ _ _ _ (hk w)
  have hhc : Continuous h := hecke_cont K hKo h fun k hk g => by simpa using hh.2 1 K.one_mem k hk g
  have hcont : ∀ φ : π.V, Continuous φ.1.1 := fun φ => DiscreteGroups.T1.G.continuous_of_mem π φ.2
  have hphi : ∀ p : (InfinitePlace E → G n) × GL (Fin n) (Af E), phiProd lam k h (split0 E n p) = (∏ w, e w (p.1 w)) * h p.2 := by
    intro p
    have e1 : ∀ w, infAt E n w (split0 E n p).1 = p.1 w := fun w => gInf_splitGA n p w
    have e2 : finOf E n (split0 E n p).1 = p.2 := gFin_splitGA n p
    simp only [phiProd, e1, e2, he]
  have hphi' : phiProd lam k h = (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2) ∘
      (split0 E n).symm.toHomeomorph := by
    funext y
    obtain ⟨p, rfl⟩ := (split0 E n).surjective y
    rw [hphi]
    exact (congrArg (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2)
      ((split0 E n).symm_apply_apply p)).symm
  have hpc : Continuous (phiProd lam k h) := by
    rw [hphi']
    exact (((prod_cs e hecs).1.comp continuous_fst).mul (hhc.comp continuous_snd)).comp (Homeomorph.continuous _)
  have hps : HasCompactSupport (phiProd lam k h) := by
    rw [hphi']
    refine HasCompactSupport.comp_homeomorph ?_ _
    refine HasCompactSupport.intro ((prod_cs e hecs).2.isCompact.prod hh.1.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h1 | h1
    · rw [show (∏ w, e w (p.1 w)) = 0 from
        image_eq_zero_of_notMem_tsupport (f := fun y : InfinitePlace E → G n => ∏ v, e v (y v)) h1, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  rw [hc (fun y => phiProd lam k h y * ψ.1.1 (x * y.1))
    (hpc.mul ((hcont ψ).comp (continuous_const.mul continuous_fst))) hps.mul_right, mul_assoc]
  congr 1
  let j : InfinitePlace E → G n → GA E n := fun w t => infP n (Pi.mulSingle w t)
  let l := (Finset.univ : Finset (InfinitePlace E)).toList
  let ih : (InfinitePlace E → G n) →* GA E n := MonoidHom.mk' (infP n) (infinitePart_mul n)
  have hjl : ∀ y : InfinitePlace E → G n, (l.map fun v => j v (y v)).prod = infP n y := by
    intro y
    have e1 : (l.map fun v => (Pi.mulSingle v (y v) : InfinitePlace E → G n)).prod = y := by
      funext w
      rw [prod_single y l (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (map_list_prod ih _).symm
    rw [List.map_map]
    rfl
  have hj : ∀ w, Continuous (j w) := fun w => (continuous_infP n).comp (continuous_mulSingle (A := fun _ => G n) w)
  have key := iter_list μC e hecs j hj (fun u => (D.i u).1.1) (fun u => hcont _) (fun w => val w (infOf (lam w))) P
    (fun w u g => by
      have := hL E n hn π hθ K hKo hKc hKθ μf D w (lam w) (hch w) ν hν μC _ _ (P w) (hP w) (k w) (val w) (T w) (hk w) u g
      simp only [along_val] at this
      exact this) l (Finset.nodup_toList _) (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) u x
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hjl, hu, heckeOp, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [hphi, mul_assoc, mul_assoc x]
  rfl
end
end

namespace UpperTheory.V.Z.Mult.Pi

open UpperTheory.V.Z.GSp4Splitting UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem global_twisted_trace_bound : GlobalTwistedTraceBound :=
  twisted_trace_global_bound_of_archimedean avgEx (absGlobA multiFac lieStab projEx avgFacts (onePlace coreG lieStab projEx avgFacts (avgTr avgFacts))) lowIso2 heckeMem
    (rlEx petEx heckeMem) rlPair rlChar rlK rlTheta rlComm (rlHecke heckeMem) (rlSimple heckeMem lieStab rlK) rlFin
    (rlLow heckeMem lowType) (opFormA locAct)

theorem absCoreA : AbsCoreA := absCoreA_pf (absCore_pf traceForm_pf) rankOne_pf corner_pf minIdem_pf

theorem levelTrA_holds : LevelTrA :=
  levelTrA adm (zTrA adm pfHecke prodOp locComm yLoc zSimple (ySwap_pf slotFacts pfHecke prodOp) (isot_pf slotFacts)
    (simpleFix_pf cvOp) absCoreA) (seenTrA trLevel adm cvOp) tTr

end UpperTheory.V.Z.Mult.Pi

open UpperTheory.V.Z.Mult.Pi UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm in
theorem UpperTheory.V.Z.Mult.piTermA : UpperTheory.V.Z.Mult.PiTermA :=
  piTermA_of global_twisted_trace_bound UpperTheory.V.Z.Tf.GOne.thetaFixOf wtEx_pf levTop levFix lcLevel_pf
    (toYdA slotFacts levTop translF_pf heckeSum_pf lvShift_pf) levelTrA_holds twUniq_pf (levIdx_pf slotFacts levTop) volIdx_pf
    (kf_top slotFacts levTop places)

/-
Cotisations sociales et patronales — règles légales françaises.

Outils numériques de base : montants (Eur), taux (Taux), puissances
rationnelles calculées en arithmétique entière exacte.

Tous les montants sont des rationnels exacts (Rat) : pas de perte de
précision dans les calculs intermédiaires. L'arrondi au centime est un
choix d'affichage laissé à l'appelant (`plancherCentimes` est fourni).
-/
namespace Cotisations

/-- Montant en euros. -/
abbrev Eur := Rat

/-- Taux exprimé en fraction de 1 (0,13 = 13 %). -/
abbrev Taux := Rat

/-- Construit un taux à partir d'un pourcentage : `pct 13 = 0,13`. -/
def pct (x : Rat) : Taux := x / 100

/-- Arrondi au centime inférieur (montants positifs). -/
def plancherCentimes (x : Eur) : Eur :=
  ((100 * x).floor.toNat : Rat) / 100

/-! ### Racine n-ième entière (méthode de Newton, arithmétique exacte) -/

/-- Une étape de Newton pour la racine n-ième de v. -/
def etapeNewton (n v y : Nat) : Nat :=
  ((n - 1) * y + v / y ^ (n - 1)) / n

/-- Descente de Newton depuis un majorant, avec garde-fou (fuel). -/
def racineDepuis (n v : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, y =>
      let y' := etapeNewton n v y
      if y' < y then racineDepuis n v fuel y' else max y 1

/-- Ajustement à la baisse : renvoie le plus grand y ≤ y0 tel que y^n ≤ v. -/
def ajusteRacineDesc (n v fuel y : Nat) : Nat :=
  match fuel with
  | 0 => y
  | fuel' + 1 => if y ^ n > v then ajusteRacineDesc n v fuel' (y - 1) else y

/-- Ajustement à la hausse : renvoie le plus petit y ≥ y0 tel que (y+1)^n > v. -/
def ajusteRacineAsc (n v fuel y : Nat) : Nat :=
  match fuel with
  | 0 => y
  | fuel' + 1 => if (y + 1) ^ n <= v then ajusteRacineAsc n v fuel' (y + 1) else y

/-- Plus grand entier y tel que y^n ≤ v (pour v ≥ 0, n ≥ 1).
    Méthode : Newton depuis 2^(log2 v / n + 1), descente monotone,
    puis ajustement final exact. -/
def racineNieme (n v : Nat) : Nat :=
  if v == 0 then 0 else
    let y0 := max (2 ^ (Nat.log2 v / n + 1)) 1
    let y1 := racineDepuis n v 300 y0
    if y1 ^ n > v then ajusteRacineDesc n v (y1 + 2) y1
    else ajusteRacineAsc n v (y1 + 2) y1

/-- x^(p/q) calculé exactement à 10⁻¹⁰ près :
    x^(p/q) · S = (x^p · S^q)^(1/q) avec S = 10¹⁰. -/
def puissanceRat (x : Rat) (p q : Nat) : Rat :=
  if x <= 0 then 0
  else
    let S : Nat := 10 ^ 10
    let v : Nat := (x.num.toNat ^ p * S ^ q) / x.den ^ p
    (racineNieme q v : Rat) / S

/-- Borne utilisée dans les tests : a ≤ x ≤ b (abbrev pour permettre
    la synthèse d'instance `Decidable` avec `native_decide`). -/
abbrev dans (x a b : Rat) : Prop := a ≤ x ∧ x ≤ b

end Cotisations

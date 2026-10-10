/-
Assiettes et tranches de plafonnement.

Découpage de l'assiette en tranches 1 (jusqu'au PASS), 2 (1 à 8 PASS)
et 3 (au-delà de 8 PASS, subsistant pour certaines contributions),
avec plafond proratisé pour les mois incomplets ou le temps partiel.
-/
import Cotisations.Parametres
import Cotisations.Organismes

namespace Cotisations

/-- Découpage d'une assiette selon les tranches de plafond. -/
structure Tranches where
  tranche1 : Eur
  tranche2 : Eur
  tranche3 : Eur
  deriving Repr, DecidableEq, Inhabited

/-- Découpe l'assiette entre tranche 1 (jusqu'au plafond), tranche 2
    (1 à 8 plafonds) et tranche 3 (au-delà de 8 plafonds).

    Remarque : sans Mathlib, les propriétés génériques du découpage
    (tranche 1 ≤ plafond, tranches positives, somme des tranches =
    assiette) ne sont pas prouvées en toute généralité ; elles sont
    vérifiées sur des cas concrets dans `Exemples.lean`. -/
def decoupeTranches (assiette plafond : Eur) : Tranches :=
  let t1 := min assiette plafond
  let t2 := max 0 (min assiette (8 * plafond) - t1)
  let t3 := max 0 (assiette - min assiette (8 * plafond))
  { tranche1 := t1, tranche2 := t2, tranche3 := t3 }

/-- Plafond mensuel proratisé (temps partiel, entrée ou sortie en cours de mois). -/
def plafondMensuelProratise (pa : ParametresAnnee) (ps : ParametresSalarie) : Eur :=
  pa.passMensuel * ps.prorataPlafond

/-- Assiette salariale de CSG/CRDS : 98,25 % du brut, avec abattement de
    11,31 % sur la fraction heures supplémentaires (exonération salariale). -/
def assietteCSGSalariale (pa : ParametresAnnee) (ps : ParametresSalarie) : Eur :=
  pa.assietteCsg * ps.brutMensuel
  + (pa.assietteCsg - pa.abattementHeuresSupSalarial) * ps.brutHeuresSupplementaires

/-- Assiette plafonnée à 4 PASS (assurance chômage, AGS). -/
def assietteQuatrePlafonds (assiette plafond : Eur) : Eur :=
  min assiette (4 * plafond)

end Cotisations
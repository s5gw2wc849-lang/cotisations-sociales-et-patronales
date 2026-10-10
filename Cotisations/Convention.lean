/-
Protection sociale complémentaire issue de la convention collective :
mutuelle (santé), prévoyance, retraite supplémentaire, caisse de congés
payés conventionnelle.

La convention collective est intégrée ici comme unique source de
cotisations complémentaires : le projet code les règles légales et
s'interfacera avec la convention applicable à l'entreprise (une seule
convention par salarié).

Contraintes légales vérifiables :
- part patronale de mutuelle ≥ 50 % du coût total (art. L911-7 CSS) ;
- prévoyance décès des cadres : cotisation ≥ 1,5 % de la tranche 1,
  prise en charge patronale ≥ 60 % (art. L911-2 CSS).
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Parametres

namespace Cotisations

/-- La part patronale de mutuelle couvre-t-elle au moins 50 % du coût ? -/
def mutuelleConforme (partPatronale mutuelleTotale : Eur) : Bool :=
  mutuelleTotale ≤ 2 * partPatronale

/-- La prévoyance cadres respecte-t-elle le minimum légal (1,5 % de la
    tranche 1, ≥ 60 % à la charge de l'employeur) ? -/
def prevoyanceCadresConforme (taux partPatronale : Rat) : Bool :=
  taux ≥ 0.015 && partPatronale ≥ 0.60

/-- Lignes salariales issues de la convention collective. -/
def lignesConventionSalariales (cc : ConventionCollective) (t : Tranches) :
    List LigneCotisation :=
  (if cc.mutuelleSalariale > 0 then
    [ { nom := "Complémentaire santé (mutuelle) — part salariale"
        organisme := .mutuelle, nature := .cotisation, cote := .salariale
        assiette := cc.mutuelleSalariale + cc.mutuellePatronale
        partSalariale := cc.mutuelleSalariale } ]
  else [])
  ++ (if cc.prevoyanceTauxT1 > 0 then
    [ { nom := "Prévoyance — part salariale"
        organisme := .prevoyance, nature := .cotisation, cote := .salariale
        assiette := t.tranche1
        partSalariale := (1 - cc.prevoyancePartPatronale) * cc.prevoyanceTauxT1 * t.tranche1 } ]
  else [])
  ++ (if cc.retraiteSupplementaireT1.tauxSalarial > 0 then
    [ { nom := "Retraite supplémentaire — T1, part salariale"
        organisme := .retraiteSupplementaire, nature := .cotisation, cote := .salariale
        assiette := t.tranche1
        partSalariale := cc.retraiteSupplementaireT1.tauxSalarial * t.tranche1 } ]
  else [])
  ++ (if cc.retraiteSupplementaireT2.tauxSalarial > 0 then
    [ { nom := "Retraite supplémentaire — T2, part salariale"
        organisme := .retraiteSupplementaire, nature := .cotisation, cote := .salariale
        assiette := t.tranche2
        partSalariale := cc.retraiteSupplementaireT2.tauxSalarial * t.tranche2 } ]
  else [])

/-- Lignes patronales issues de la convention collective. -/
def lignesConventionPatronales (cc : ConventionCollective) (t : Tranches) :
    List LigneCotisation :=
  (if cc.mutuellePatronale > 0 then
    [ { nom := "Complémentaire santé (mutuelle) — part patronale"
        organisme := .mutuelle, nature := .cotisation, cote := .patronale
        assiette := cc.mutuelleSalariale + cc.mutuellePatronale
        partPatronale := cc.mutuellePatronale } ]
  else [])
  ++ (if cc.prevoyanceTauxT1 > 0 then
    [ { nom := "Prévoyance — part patronale"
        organisme := .prevoyance, nature := .cotisation, cote := .patronale
        assiette := t.tranche1
        partPatronale := cc.prevoyancePartPatronale * cc.prevoyanceTauxT1 * t.tranche1 } ]
  else [])
  ++ (if cc.retraiteSupplementaireT1.tauxPatronal > 0 then
    [ { nom := "Retraite supplémentaire — T1, part patronale"
        organisme := .retraiteSupplementaire, nature := .cotisation, cote := .patronale
        assiette := t.tranche1
        partPatronale := cc.retraiteSupplementaireT1.tauxPatronal * t.tranche1 } ]
  else [])
  ++ (if cc.retraiteSupplementaireT2.tauxPatronal > 0 then
    [ { nom := "Retraite supplémentaire — T2, part patronale"
        organisme := .retraiteSupplementaire, nature := .cotisation, cote := .patronale
        assiette := t.tranche2
        partPatronale := cc.retraiteSupplementaireT2.tauxPatronal * t.tranche2 } ]
  else [])
  ++ (if cc.tauxCaisseCongesPayes > 0 then
    [ { nom := "Caisse de congés payés / intempéries (conventionnelle)"
        organisme := .caisseCongesPayes, nature := .cotisation, cote := .patronale
        assiette := t.tranche1 + t.tranche2 + t.tranche3
        partPatronale := cc.tauxCaisseCongesPayes * (t.tranche1 + t.tranche2 + t.tranche3) } ]
  else [])

end Cotisations
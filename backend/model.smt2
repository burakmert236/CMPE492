;; activate model generation
(set-option :produce-models true)
(set-option :opt.priority lex)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool)
(declare-fun G2 () Bool)
(declare-fun G3 () Bool)
(declare-fun G4 () Bool)
(declare-fun R1 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R1 )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G3 )) (=> R1 G1 )))

;;%%%%
;Mandatory goals
;%%%%
(assert G1)

;;%%%%
;Implemented goals
;%%%%

;;%%%%
;Precedence relationships
;%%%%

;;%%%%
;Contributions
;%%%%

;;%%%%
;Goal Attributes
;%%%%
(assert-soft (not G1) :weight 1 :id cost)
(assert-soft (not G1) :weight 1 :id value)
(assert-soft (not G2) :weight 1 :id cost)
(assert-soft (not G2) :weight 1 :id value)
(assert-soft (not G3) :weight 1 :id cost)
(assert-soft (not G3) :weight 1 :id value)

;;%%%%
;Exclusion
;%%%%
(assert (not (and G1 G2)))

;;%%%%
;Leaf Nodes
;%%%%
(assert-soft (not G3 ) :id sat_tasks)

;;%%%%
;Root Nodes
;%%%%
(assert-soft (not G1 ) :id unsat_requirements)
(assert-soft (not G2 ) :id unsat_requirements)
(assert-soft (not G4 ) :id unsat_requirements)

;;%%
;;Optimization:
;;%%
(declare-fun cost.auto () Real)
(assert (= cost.auto (- cost 0)))
(declare-fun value.auto () Real)
(assert (= value.auto (- value 0)))


(minimize cost.auto)
(maximize value.auto)
(check-sat)
(get-objectives)
(load-objective-model 1)
(get-model)
(exit)

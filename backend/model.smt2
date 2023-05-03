;; activate model generation
(set-option :produce-models true)
(set-option :opt.priority lex)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool)
(declare-fun G2 () Bool)
(declare-fun G3 () Bool)
(declare-fun G5 () Bool)
(declare-fun G6 () Bool)
(declare-fun G7 () Bool)
(declare-fun G8 () Bool)
(declare-fun R2 () Bool)
(declare-fun R3 () Bool)
(declare-fun R4 () Bool)
(declare-fun R1 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R4  )))
(assert (=> G2 (or R2 )))
(assert (=> G3 (or R1 )))
(assert (=> G7 (or R3 )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G6 )) (=> R1 G3 )))
(assert (and (= R2 (and G5 )) (=> R2 G2 )))
(assert (and (= R3 (and G8 )) (=> R3 G7 )))
(assert (and (= R4 (and G2 G3 )) (=> R4 G1 )))

;;%%%%
;Mandatory goals
;%%%%

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
(assert-soft (not G5) :weight 1 :id cost)
(assert-soft (not G5) :weight 1 :id value)
(assert-soft (not G6) :weight 1 :id cost)
(assert-soft (not G6) :weight 1 :id value)
(assert-soft (not G7) :weight 1 :id cost)
(assert-soft (not G7) :weight 1 :id value)
(assert-soft (not G8) :weight 1 :id cost)
(assert-soft (not G8) :weight 1 :id value)

;;%%%%
;Leaf Nodes
;%%%%
(assert-soft (not G5 ) :id sat_tasks)
(assert-soft (not G6 ) :id sat_tasks)
(assert-soft (not G8 ) :id sat_tasks)

;;%%%%
;Root Nodes
;%%%%
(assert-soft (not G1 ) :id unsat_requirements)
(assert-soft (not G7 ) :id unsat_requirements)

;;%%
;;Optimization:
;;%%
(declare-fun cost.auto () Real)
(assert (= cost.auto (- cost 0)))
(declare-fun value.auto () Real)
(assert (= value.auto (- value 0)))


(minimize cost.auto)
(maximize value.auto)
(minimize unsat_requirements)
(minimize sat_tasks)
(check-sat)
(get-objectives)
(load-objective-model 1)
(get-model)
(exit)

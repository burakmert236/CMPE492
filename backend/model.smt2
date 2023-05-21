;; activate model generation
(set-option :produce-models true)
(set-option :opt.priority lex)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%

;;%%%%
;Close-world
;%%%%

;;%%%%
;Refinement-Goal relationships
;%%%%

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

;;%%%%
;Exclusion
;%%%%

;;%%%%
;Leaf Nodes
;%%%%

;;%%%%
;Root Nodes
;%%%%

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

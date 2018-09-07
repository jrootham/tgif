(ns sat.core
  (:gen-class)
  (:require [clojure.set :refer [intersection difference union]])
  (:require [clojure.string :as str])
)

(defn parse-clause [line]
	(loop [literals (str/split line #" ") sat-true #{} sat-false #{}] 
		(if (empty? literals)

			{:sat-true sat-true :sat-false sat-false}

			(let 
				[
					this-one (first literals)
					remaining (rest literals)
				]

				(if (str/starts-with? this-one "~")
					(recur remaining sat-true (conj sat-false (subs this-one 1)))
					(recur remaining (conj sat-true this-one) sat-false)
				)
			)		
		)
	)
)

(defn get-cnf []
	(loop [line (read-line) result ()] 
		(if line
			(if (or (str/starts-with? line "~ ") (str/blank? line))
				(recur (read-line) result)
				(recur (read-line) (cons (parse-clause line) result)) 
			) 

			result
		)	
	)
)

(defn simplify [raw-cnf]
	(loop [clause-list raw-cnf result ()]
		(if (empty? clause-list)
			result
			(let 
				[
					clause (first clause-list)
					input-sat-true (get clause :sat-true)
					input-sat-false (get clause :sat-false)
					tautology (intersection input-sat-true input-sat-false)
					sat-true (difference input-sat-true tautology)
					sat-false (difference input-sat-false tautology)
				]
				(if (and (empty? sat-true) (empty? sat-false))
					(recur (rest clause-list) result)
					(recur (rest clause-list) (cons {:sat-true sat-true :sat-false sat-false} result))
				)
			)
		)
	)
)

(defn get-size [raw-cnf]
	(loop [clause-list raw-cnf literal-set #{}]
		(if (empty? clause-list)
			(count literal-set)
			(let
				[
					clause (first clause-list)					
					sat-true (get clause :sat-true)
					sat-false (get clause :sat-false)
				]
				(recur (rest clause-list) (union literal-set (union sat-true sat-false)))
			)
		)
	)
)

(defn make-side [sat-set jump-level]
	{:sat-set sat-set :jump-level jump-level}
)

(defn make-record [sat-true sat-false jump-level]
	{:true-side (make-side sat-true jump-level) :false-side (make-side sat-false jump-level)}
)

(defn make-cnf [raw-cnf size]
	(loop [clause-list raw-cnf result ()]
		(if (empty? clause-list)
			result
			(let
				[
					clause (first clause-list)					
					sat-true (get clause :sat-true)
					sat-false (get clause :sat-false)
				]
				(recur (rest clause-list) (cons (make-record sat-true sat-false size) result))
			)
		)
	)
)

(defn unit? [sat-true sat-false]
	(= 1 (+ (count sat-true) (count sat-false)))
)

(defn end-scan [options cnf input stats]
	(let 
		[
			true-unit (get input :true-unit)
			false-unit (get input :false-unit)
		]
		(if (= 0 (count (intersection true-unit false-unit)))
			{:sat true}
			{:sat false}
		)
	)		
)

(defn do-clause [options clause cnf assert-literals input stats]
	(let
		[
			sat-true (get (get clause :true-side) :sat-set)
			sat-false (get (get clause :false-side) :sat-set)
			true-set (union (get input :true-set) sat-true)
			false-set (union (get input :false-set) sat-false)
			true-unit (union (get input :true-unit) (if (unit? sat-true sat-false) sat-true #{}))
			false-unit (union (get input :false-unit) (if (unit? sat-true sat-false) sat-false #{}))
		]

		{
			:cnf cnf
			:input 
				{
					:true-set true-set
					:false-set false-set
					:true-unit true-unit
					:false-unit false-unit
				}
			:stats stats
		}
	)
)
 
(defn scan-cnf [options base-cnf level assert-literals stats]
	(loop 
		[
			clause-list base-cnf 
			cnf ()
			input {:true-set #{} :false-set #{} :true-unit #{} :false-unit #{}} 
		]
		(if (empty? clause-list)
			(end-scan options cnf input stats)
			(let
				[
					clause (first clause-list)					
					clause-result (do-clause options clause cnf assert-literals input)
					new-cnf (get clause-result :cnf)
					input (get clause-result :input)
				]
				(recur (rest clause-list) new-cnf input)
			)
		)
	)
)

(defn -main
	"SAT solver"
	[& args]
	(let 
		[
			raw-cnf (simplify (get-cnf))
			infinity (+ 1 (get-size raw-cnf))
			cnf (make-cnf raw-cnf infinity)
		]
		(println (scan-cnf {} cnf 0 {:true-side #{} :false-side #{}} {}))
	)
)


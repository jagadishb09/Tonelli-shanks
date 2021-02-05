
(in-package "ACL2")

(include-book "std/util/define" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(define Q*2^S ((n natp))
  :returns (mv (q natp) (s natp))
  :verify-guards nil
  (if (or (not (natp n)) (= n 0))
      (mv 0 0)
    (if (oddp n)
        (mv n 0)
      (mv-let (inner-q inner-s)
	      (Q*2^S (/ n 2))
	      (mv inner-q (+ inner-s 1)))))
  ///
  (verify-guards Q*2^S))

(defthm q2s-q-is-odd
  (implies (and (natp n) (< 0 n) (oddp n))
           (oddp (mv-nth 0 (Q*2^S n))))
  :hints (("Goal" :in-theory (e/d (Q*2^S) (oddp)))))

(defthmd q2s-is-correct-1
  (implies (integerp y)
	   (equal (expt 2 (+ 1 y))
		  (* 2 (expt 2 y))))
  :hints (("Goal"
	   :in-theory (enable expt)))
  
  )

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd q2s-is-correct-2-1-1
   (= (* a b c) (* b a c))
   )
 
 (defthmd q2s-is-correct-2-1
   (implies (integerp a)
	    (= (* x (expt 2 (+ 1 a)))
	       (* 2 (* x (expt 2 a)))))
   :hints (("Goal"
	    :use ((:instance q2s-is-correct-1 (y a))
		  (:instance q2s-is-correct-2-1-1 (a x) (b 2) (c (expt 2 a)))
		  ;; (:instance associativity-of-*
		  ;; 	    (x x)
		  ;; 	    (y 2)
		  ;; 	    (z (expt 2 a)))
		  ;; (:instance commutativity-of-*
		  ;; 	    (x x)
		  ;; 	    (y 2))
		  ;; (:instance associativity-of-*
		  ;; 	    (y x)
		  ;; 	    (x 2)
		  ;; 	    (z (expt 2 a)))
		  )
					;:do-not-induct t
	    :in-theory nil
	    ))
   )
 )



(defthmd q2s-is-correct-2
  (IMPLIES (AND (EQUAL (EXPT 2 (+ 1 (MV-NTH 1 (Q*2^S (* N 1/2)))))
		       (* 2
			  (EXPT 2 (MV-NTH 1 (Q*2^S (* N 1/2))))))
		(INTEGERP (MV-NTH 1 (Q*2^S (* N 1/2))))
		(INTEGERP (* 1/2 N))
		(EQUAL (* (MV-NTH 0 (Q*2^S (* N 1/2)))
			  (EXPT 2 (MV-NTH 1 (Q*2^S (* N 1/2)))))
		       (* 1/2 N))
		(INTEGERP N)
		(<= 0 N)
		(< 0 N))
	   (EQUAL (* (MV-NTH 0 (Q*2^S (* N 1/2)))
		     (EXPT 2 (+ 1 (MV-NTH 1 (Q*2^S (* N 1/2))))))
		  N))
  :hints (("Goal"
	   :use(
		(:instance q2s-is-correct-2-1
			   (a (MV-NTH 1 (Q*2^S (* N 1/2))))
			   (x (MV-NTH 0 (Q*2^S (* N 1/2)))))
		
		)
	   :in-theory nil
	   ))
  )

(defthm q2s-is-correct                                                                                                                                                                            
  (implies (and (natp n) (< 0 n)                                                                                                                                                                  
                (equal (mv-nth 0 (Q*2^S n)) q)                                                                                                                                                    
                (equal (mv-nth 1 (Q*2^S n)) s))                                                                                                                                                   
           (equal (* q (expt 2 s)) n))
  :hints (("Goal" :in-theory (e/d (Q*2^S) ()))
	  ("Subgoal *1/6"
	   :cases ((INTEGERP (MV-NTH 1 (Q*2^S (* N 1/2)))))
	   )
	  
	  ("Subgoal *1/6.1"
	   :use ((:instance  q2s-is-correct-1 (y (MV-NTH 1 (Q*2^S (* N 1/2)))))
		 (:instance q2s-is-correct-2 (n n)))
	   )
	  )
  )

#||                                                                                                                                                                                               

;; How about something like this.                                                                                                                                                                 
;; What hints will get it to work, or how can it be restructured                                                                                                                                  
;; to work?                                                                                                                                                                                       



||#



(in-package "PRIMES")

;(include-book "std/util/define" :dir :system)
;(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(include-book "kestrel/number-theory/tonelli-shanks-test" :dir :system)
;(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))
;(local (include-book "projects/quadratic-reciprocity/eisenstein" :dir :system))

(local (include-book "kestrel/crypto/ecurve/primes" :dir :system))

(include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
(include-book "projects/quadratic-reciprocity/euclid" :dir :system)

(local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

(defthm y^2=1modp-lemma1
  (implies (and (integerp a)
                (integerp b)
                (rtl::primep p)
                (rtl::divides p (* a b))
                (not (rtl::divides p b)))
           (rtl::divides p a))
  :hints (("Goal"
           :use (:instance rtl::euclid (p p) (a a) (b b))
           ))
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm y^2=1modp
    (implies (and (rtl::primep p)
                  (integerp y)
                  (> p 2)
                  (= (mod (* y y) p) 1))
             (or (= (mod y p) 1)
                 (= (mod y p) (mod -1 p))))
    :hints (("Goal"
             :cases ((rtl::divides p (- y 1))
                     (rtl::divides p (+ y 1)))
             )
            ("Subgoal 3"
             :use ((:instance rtl::divides-mod-equal (n p) (a (* y y)) (b 1))
                   (:instance y^2=1modp-lemma1 (a (- y 1)) (b (+ y 1))))          
             )
            ("Subgoal 2"
             :use (:instance rtl::divides-mod-equal (n p) (a y) (b 1))
             )
            ("Subgoal 1"
             :use (:instance rtl::divides-mod-equal (n p) (a y) (b -1))
             :in-theory (e/d (rtl::primep) ())
             )
            )
    )
  )

(defthmd least-repeated-square-aux-not=0-1
  (implies (and (natp tt)
                (natp M)
                (natp p)
                (natp i)
                (<= 0 i)
                (< 2 p)
                (equal (least-repeated-square-aux i tt m p) lrs)
                (not (= lrs 0)))
           (and (= (mod (expt tt (expt 2 lrs)) p) 1)
                (< lrs M)
                (< i M)))
  :hints (("Goal"
           :in-theory (enable acl2::mod-expt-fast)
           ))
  )

(defthmd least-repeated-square-aux-not=0
  (implies (and (natp tt)
                (natp M)
                (natp p)
                (< 2 p)
                (equal (least-repeated-square-aux 0 tt m p) lrs)
                (not (= lrs 0)))
           (and (= (mod (expt tt (expt 2 lrs)) p) 1)
                (< lrs M)
                (< 0 M)))
  :hints (("Goal"
           :use (:instance least-repeated-square-aux-not=0-1 (i 0) (tt tt) (m m)
                           (p p) (lrs (least-repeated-square-aux 0 tt m p)))
           :in-theory (enable acl2::mod-expt-fast)
           ))
  )

(defthmd least-repeated-square-aux-not=0-2-1
  (implies (and (natp tt)
                (natp M)
                (natp p)
                (natp i)
                (<= 0 i)
                (< 2 p)
                (natp d)
                (< d i)
                (> d 0)
                (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX I TT M P)
                            0)))
           (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX d TT M P)
                       0))))

(defthmd least-repeated-square-aux-not=0-2
  (implies (and (natp tt)
                (natp m)
                (natp p)
                (natp i)
                (< i m)
                (< 2 p)
                (not (= (least-repeated-square-aux i tt m p) 0))
                (not (= (mod tt p) 1)))
           (not (= (least-repeated-square-aux 0 tt m p) 0)))
  :hints (("Goal"
           :in-theory (enable acl2::mod-expt-fast)
           )
          ("Subgoal *1/1"
           :cases ((= i 0)
                   (= i 1)
                   (= i 2))
           :use (:instance least-repeated-square-aux-not=0-2-1 (d 2)
                           (i i)
                           (tt tt)
                           (m m)
                           (p p))
           ))
  )

(defthm least-repeated-square-not=0
  (implies (and (natp tt)
                (natp m)
                (natp p)
                (natp i)
                (< i m)
                (< 2 p)
                (< 0 m)
                (= (mod (expt tt (expt 2 i)) p) 1))
           (= (mod (expt tt (expt 2 (least-repeated-square tt m p))) p) 1))
  :hints (("Goal"
           :in-theory (enable acl2::mod-expt-fast)
           :cases ((= i 0)
                   (> i 0))         
           )
          ("Subgoal 1"
           :use (
                 (:instance least-repeated-square-aux-not=0-1
                            (tt tt) (m m) (p p) (lrs i) (i i))
                 (:instance least-repeated-square-aux-not=0-2
                            (tt tt) (m m) (p p) (i i))
                 (:instance least-repeated-square-aux-not=0
                            (tt tt) (m m) (p p)
                            (lrs (least-repeated-square-aux 0 tt m p)))
                 )
           )
          )
  )

(encapsulate
  ()

  (local
   (defthm least-repeated-square-aux-not=0-9-2
     (IMPLIES (AND (AND (NATP D) (NATP M) (< D M))
                   (NOT (= (ACL2::MOD-EXPT-FAST TT (EXPT 2 D) P)
                           1))
                   (IMPLIES (AND (NATP TT)
                                 (NATP M)
                                 (NATP P)
                                 (< 2 P)
                                 (NATP (+ D 1))
                                 (<= 0 (+ D 1))
                                 (< (+ D 1) M)
                                 (EQUAL (LEAST-REPEATED-SQUARE-AUX (+ D 1)
                                                                   TT M P)
                                        (+ D 1))
                                 (NATP I)
                                 (< I (+ D 1)))
                            (<= (LEAST-REPEATED-SQUARE-AUX I TT M P)
                                (+ D 1))))
              (IMPLIES (AND (NATP TT)
                            (NATP M)
                            (NATP P)
                            (< 2 P)
                            (NATP D)
                            (<= 0 D)
                            (< D M)
                            (EQUAL (LEAST-REPEATED-SQUARE-AUX D TT M P)
                                   D)
                            (NATP I)
                            (< I D))
                       (<= (LEAST-REPEATED-SQUARE-AUX I TT M P)
                           D)))
     )
   )

  (defthm least-repeated-square-aux-not=0-9
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square-aux d tt m p) d)
                  (natp i)
                  (< i d))
             (<= (least-repeated-square-aux i tt m p) d))
    )

  (local
   (defthm least-repeated-square-aux-not=0-10*1/2
     (implies (and (natp i)
                   (natp m)
                   (< i m))
              (or (>= (LEAST-REPEATED-SQUARE-AUX i TT M P) i)
                  (= (LEAST-REPEATED-SQUARE-AUX i TT M P) 0))))
   )

  (local
   (defthm least-repeated-square-aux-not=0-10*1/2.2
     (IMPLIES (AND (INTEGERP I)
                   (INTEGERP M)
                   (<= 0 M)
                   (< I M)
                   (NOT (EQUAL (MOD (EXPT TT (EXPT 2 I)) P) 1))
                   (INTEGERP TT)
                   (<= 0 TT)
                   (INTEGERP P)
                   (<= 0 P)
                   (< 2 P)
                   (< 0 M)
                   (NOT (EQUAL (MOD TT P) 1))
                   (< 1 M)
                   (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX 2 TT M P)
                               0))
                   (NOT (EQUAL (MOD (EXPT TT 2) P) 1))
                   (< I (LEAST-REPEATED-SQUARE-AUX 2 TT M P)))
              (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                     TT M P)
                          I)))
     :hints (("Goal"
              :use (:instance least-repeated-square-aux-not=0-10*1/2
                              (i (+ i 1))
                              (m m)
                              )
              ))
     )
   )

  (local
   (defthm least-repeated-square-aux-not=0-10*1/2.1
     (IMPLIES (AND (EQUAL (LEAST-REPEATED-SQUARE-AUX 2 TT M P)
                          (+ 1 I))
                   (INTEGERP I)
                   (INTEGERP M)
                   (<= 0 M)
                   (< I M)
                   (NOT (EQUAL (MOD (EXPT TT (EXPT 2 I)) P) 1))
                   (INTEGERP TT)
                   (<= 0 TT)
                   (INTEGERP P)
                   (<= 0 P)
                   (< 2 P)
                   (< 0 M)
                   (NOT (EQUAL (MOD TT P) 1))
                   (< 1 M)
                   (NOT (EQUAL (MOD (EXPT TT 2) P) 1)))
              (NOT (EQUAL (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                     TT M P)
                          I)))
     :hints (("Goal"
              :use (:instance least-repeated-square-aux-not=0-10*1/2
                              (i (+ i 1))
                              (m m)
                              )
              ))
     )
   )
  
  (defthm least-repeated-square-aux-not=0-10
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square-aux 0 tt m p) d)
                  (not (= d 0))
                  (natp i)
                  (< i d))
             (not (= (least-repeated-square-aux i tt m p) i)))
    :hints (("Goal"
             :in-theory (enable acl2::mod-expt-fast)
             )
            ("Subgoal *1/1"
             :cases ((= i 0)
                     (= i 1)
                     (= i 2)
                     (> i 2))
             :use (:instance least-repeated-square-aux-not=0-9
                             (tt tt) (m m) (p p)
                             (i 2) (d i))
             )
            )
    )

  (defthm least-repeated-square-is-least
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square tt m p) d)
                  (not (= d 0))
                  (natp i)
                  (< i d))
             (not (= (mod (expt tt (expt 2 i)) p) 1)))
    :hints (("Goal"
             :use (
                   (:instance least-repeated-square-aux-not=0
                              (tt tt)
                              (m m)
                              (p p)
                              (lrs d))                          
                   (:instance least-repeated-square-aux-not=0-10
                              (tt tt)
                              (m m)
                              (p p)
                              (i i)
                              (d d))
                   )
             :in-theory (enable acl2::mod-expt-fast)
             ))
    )
  )

(encapsulate
  ()
  (local
   (defthm least-repeated-square-aux-not=0-9-2
     (IMPLIES (AND (AND (NATP D) (NATP M) (< D M))
                   (NOT (= (ACL2::MOD-EXPT-FAST TT (EXPT 2 D) P)
                           1))
                   (IMPLIES (AND (NATP TT)
                                 (NATP M)
                                 (NATP P)
                                 (< 2 P)
                                 (NATP (+ D 1))
                                 (<= 0 (+ D 1))
                                 (< (+ D 1) M)
                                 (EQUAL (LEAST-REPEATED-SQUARE-AUX (+ D 1)
                                                                   TT M P)
                                        (+ D 1))
                                 (NATP I)
                                 (< I (+ D 1)))
                            (<= (LEAST-REPEATED-SQUARE-AUX I TT M P)
                                (+ D 1))))
              (IMPLIES (AND (NATP TT)
                            (NATP M)
                            (NATP P)
                            (< 2 P)
                            (NATP D)
                            (<= 0 D)
                            (< D M)
                            (EQUAL (LEAST-REPEATED-SQUARE-AUX D TT M P)
                                   D)
                            (NATP I)
                            (< I D))
                       (<= (LEAST-REPEATED-SQUARE-AUX I TT M P)
                           D)))
     )
   )

  (defthmd least-repeated-square-aux-not=0-9
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square-aux d tt m p) d)
                  (natp i)
                  (< i d))
             (<= (least-repeated-square-aux i tt m p) d))
    )
  )

(defthm mod-expt-fast-instance-meaning
  (implies (and (rtl::primep p)
                (fep m p))
           (equal (acl2::mod-expt-fast m (/ (- p 1) 2) p)
                  (mod (expt m (/ (1- p) 2)) p)))
  :hints (("Goal" :in-theory (enable acl2::mod-expt-fast))))

(defthm T-S-aux-euler-criterion-lemma1
  (implies (and (rtl::primep p)
                (< 2 p))
           (oddp p))
  :hints (("Goal"
           :in-theory (e/d (rtl::primep) (oddp))
           ))
  )

(defthm T-S-aux-euler-criterion
  (implies (and (rtl::primep p)
                (> p 2)
                (integerp n)
                (< n p)
                (> n 0))
           (equal (mod (expt n (/ (- p 1) 2)) p)
                  (if (has-square-root? n p) 1 (mod -1 p))))
  :hints (("Goal"
           :use ((:instance mod-expt-fast-instance-meaning (m n) (p p))
                 (:instance residue-meaning (p p) (m n))
                 (:instance rtl::euler-criterion (p p) (m n))
                 (:instance T-S-aux-euler-criterion-lemma1 (p p))
                 )
           :in-theory (enable acl2::mod-expt-fast rtl::primep)
           ))
  )

(skip-proofs
 (defthm t-s-aux-equiv-lemma1-2
   (implies (and (natp z)
                 (rtl::primep p)
                 (natp p)
                 (< 2 p)
                 (= z 0))
            (has-square-root? z p))
;(> z 0))
   :hints (("Goal"
            :cases ((= z 0))
            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) ())
            :do-not-induct t
            ))
   )
 )

(encapsulate
  ()

  (local
   (defthmd t-s-aux-equiv-lemma1-1
     (implies (and (integerp a)
                   (integerp p)
                   (> p 0))
              (equal (mod (* a (mod a p)) p)
                     (mod (* a a) p))))
   )

  
  (defthm t-s-aux-equiv-lemma1
    (IMPLIES
     (AND (INTEGERP N)
          (<= 0 N)
          (<= 0 P)
          (INTEGERP Z)
          (<= 0 Z)
          (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
                      1))
          (< 2 P)
          (< Z P)
          (RTL::PRIMEP P)
          (< N P)
          (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
                 1)
          (< 0 N)
          (INTEGERP X)
          (<= 0 X)
          (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 X))) P)
                 (+ -1 P))
          (INTEGERP M)
          (< 0 M)
          (INTEGERP C)
          (<= 0 C)
          (INTEGERP TT)
          (<= 0 TT)
          (INTEGERP R)
          (<= 0 R)
          (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
          (EQUAL (MOD (EXPT TT
                            (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
                      P)
                 1)
          (< 0 (LEAST-REPEATED-SQUARE TT M P)))
     (EQUAL
      (MOD (* R
              (EXPT C
                    (EXPT 2
                          (+ -1
                             M (- (LEAST-REPEATED-SQUARE TT M P)))))
              (MOD (* R
                      (EXPT C
                            (EXPT 2
                                  (+ -1
                                     M (- (LEAST-REPEATED-SQUARE TT M P))))))
                   P))
           P)
      (MOD (* N TT
              (EXPT C
                    (EXPT 2
                          (+ -1
                             M (- (LEAST-REPEATED-SQUARE TT M P)))))
              (EXPT C
                    (EXPT 2
                          (+ -1
                             M (- (LEAST-REPEATED-SQUARE TT M P))))))
           P)))
    :hints (("Goal"
             :use ((:instance t-s-aux-equiv-lemma1-1
                              (a (* R
                                    (EXPT C
                                          (EXPT 2
                                                (+ -1
                                                   M (- (LEAST-REPEATED-SQUARE
                                                         TT M P)))))))
                              (p p))
                   (:instance rtl::mod-times-mod
                              (a (* R R))
                              (b (* N tt))
                              (c
                               (* (EXPT C
                                        (EXPT 2
                                              (+ -1
                                                 M (- (LEAST-REPEATED-SQUARE TT M P)))))
                                  (EXPT C
                                        (EXPT 2
                                              (+ -1
                                                 M (- (LEAST-REPEATED-SQUARE TT
                                                                             M P))))))
                               )
                              (n p))
                   )
             :in-theory (e/d () (least-repeated-square))
             ))
    )
  
  (defthm t-s-aux-equiv
    (implies (and (natp n)
                  (natp p)
                  (natp z)
                  (not (has-square-root? z p))
                  (< 2 p)
                  (< z p)
                  (rtl::primep p)
                  (< n p)
                  (has-square-root? n p)
                  (< 0 n)

                  (posp x);; x = S
                  (equal (mod (expt c (expt 2 (- x 1))) p) (mod -1 p)) ;; c = (acl2::mod-expt-fast z Q p)
;variables don't change                

                  (posp M) ; M =S
                  (natp c) ; (acl2::mod-expt-fast z Q p)
                  (natp tt) ; (acl2::mod-expt-fast n Q p)
                  (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

                  (equal (mod (* R R) p) (mod (* tt n) p))
                  (equal (least-repeated-square tt M p) M2)
                  (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
             
             (if (zp M2)
                 (and (equal (mod (* R R) p) (mod n p))
                      (equal (T-S-aux M c tt R p) R)
                      )
               
               (let ((b (expt c (expt 2 (- (- M M2) 1)))))
                 (let (
                       (c2 (mod (* b b) p))
                       (tt2 (mod (* tt b b) p))
                       (R2 (mod (* R b) p)))
                   (and (natp n)
                        (natp p)
                        (natp z)
                        (not (has-square-root? z p))
                        (< 2 p)
                        (< z p)
                        (rtl::primep p)
                        (< n p)
                        (has-square-root? n p)
                        (< 0 n)

                        (posp x);; x = S
                        (equal (mod (expt c (expt 2 (- x 1))) p) (mod -1 p)) ;; c = z^Q
;variables don't change                

                        (posp M2) ; M =S
                        (natp c2) ; (acl2::mod-expt-fast z Q p)
                        (natp tt2) ; (acl2::mod-expt-fast n Q p)
                        (natp R2) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

                        (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
;(equal (least-repeated-square tt2 M2 p) M3)
                        (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)

                        (< M2 M)
                        
                        (equal (T-S-aux M c tt R p)
                               (T-S-aux M2 c2 tt2 R2 p)))))))
    
    :hints (("Goal"
;:use (:instance least-repeated-square-equiv-2 (tt tt) (m e) (p p))
             :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square))
             :do-not-induct t
             ))
    )
  )

(defthm hyps-true-T-S-aux
  (implies (and (natp n)
                (natp p)
                (natp z)
                (not (has-square-root? z p))
                (< 2 p)
                (< z p)
                (rtl::primep p)
                (< n p)
                (has-square-root? n p)
                (< 0 n)

                (equal (mv-nth 1 (Q*2^S (- p 1))) x)

                (equal (mv-nth 1 (Q*2^S (- p 1))) M)
                (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
                (equal (acl2::mod-expt-fast z Q p) c)
                (equal (acl2::mod-expt-fast n Q p) tt)
                (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R)

                (equal (least-repeated-square tt M p) M2))
           
           (and (posp x)
                (posp M) ; M =S
                (natp c) ; (acl2::mod-expt-fast z Q p)
                (natp tt) ; (acl2::mod-expt-fast n Q p)
                (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

                (equal (mod (* R R) p) (mod (* tt n) p))
                
                (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)))
  :hints (("Goal"
;:use (:instance least-repeated-square-equiv-2 (tt tt) (m e) (p p))
           :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square))
           :do-not-induct t
           ))
  )
                 


                 
                 (and (natp tt2)
                      (rtl::primep p)
                      (< 2 p)
                      (< 0 m2)
                      (natp M2)
                      (natp x)
                      (equal (mod (expt c (expt 2 (- x 1))) p) (mod -1 p))
                      (integerp R2)
                      (integerp c2)
                      (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
                      (equal (T-S-aux e c tt R p) (T-S-aux M2 c2 tt2 R2 p)))))))
  :hints (("Goal"
;:use (:instance least-repeated-square-equiv-2 (tt tt) (m e) (p p))
           :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square))
           :do-not-induct t
           ))
  )



(defthm t-s-aux-equiv-lemma1
  (IMPLIES
   (AND (natp n)
        (< n p)
        (<= 0 P)
        (< 2 P)
        (RTL::PRIMEP P)
        (INTEGERP TT)
        (<= 0 TT)
        (< 0 E)
        (INTEGERP E)
        (<= 0 E)
        (INTEGERP C)
        (natp x)
        (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 X))) P)
               (+ -1 P))
        (INTEGERP R)
        (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
        (< 0 (LEAST-REPEATED-SQUARE TT E P)))
   (EQUAL
    (MOD (* R
            (EXPT C
                  (EXPT 2
                        (+ -1
                           E (- (LEAST-REPEATED-SQUARE TT E P)))))
            (MOD (* R
                    (EXPT C
                          (EXPT 2
                                (+ -1
                                   E (- (LEAST-REPEATED-SQUARE TT E P))))))
                 P))
         P)
    (MOD (* N TT
            (EXPT C
                  (EXPT 2
                        (+ -1
                           E (- (LEAST-REPEATED-SQUARE TT E P)))))
            (EXPT C
                  (EXPT 2
                        (+ -1
                           E (- (LEAST-REPEATED-SQUARE TT E P))))))
         P)))
  :hints (("Goal"
           :use ((:instance t-s-aux-equiv-lemma1-1
                            (a (* R
                                  (EXPT C
                                        (EXPT 2
                                              (+ -1
                                                 E (- (LEAST-REPEATED-SQUARE
                                                       TT E P)))))))
                            (p p))
                 (:instance rtl::mod-times-mod
                            (a (* R R))
                            (b (* N tt))
                            (c
                             (* (EXPT C
                                      (EXPT 2
                                            (+ -1
                                               E (- (LEAST-REPEATED-SQUARE TT E P)))))
                                (EXPT C
                                      (EXPT 2
                                            (+ -1
                                               E (- (LEAST-REPEATED-SQUARE TT
                                                                           E P))))))
                             )
                            (n p))
                 )
           :in-theory (e/d () (least-repeated-square))
           ))
  )

;; add there exists i such that tt^2^i = 1 (mod p)
;; if there exists an i then (least-repeated-square tt e p) returns least
;; number m such that m < e and m>=0 and tt^2^m = 1 mod p
(defthm t-s-aux-equiv
  (implies (and (natp n)
                (natp p)
                (natp z)
                (> z 0)
                (< 2 p)
                (< z p)
                (rtl::primep p)
                (< n p)
                (has-square-root? n p)
                (not (has-square-root? z p))
                
                (natp tt) ;; n^Q
                (< 0 e)
                (natp e) ;; e = S
;(equal (least-repeated-square tt e p) m)
                (integerp c)
                (natp x);; x = S
                (equal (mod (expt c (expt 2 (- x 1))) p) (mod -1 p)) ;; c = z^Q
                (integerp R) ;;R=(n^(Q+1/2))
                (equal (mod (* R R) p) (mod (* tt n) p)))
           (let ((m (least-repeated-square tt e p)))
             (if (zp m)
                 (and (equal (mod (* R R) p) (mod n p))
                      (equal (T-S-aux e c tt R p) R)
                      )
               (let ((b (expt c (expt 2 (- (- e m) 1)))))
                 (let ((M2 m)
                       (c2 (mod (* b b) p))
                       (tt2 (mod (* tt b b) p))
                       (R2 (mod (* R b) p)))
                   (and (natp tt2)
                        (rtl::primep p)
                        (< 2 p)
                        (< 0 m2)
                        (natp M2)
                        (natp x)
                        (equal (mod (expt c (expt 2 (- x 1))) p) (mod -1 p))
                        (integerp R2)
                        (integerp c2)
                        (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
                        (equal (T-S-aux e c tt R p) (T-S-aux M2 c2 tt2 R2 p))))))))
  :hints (("Goal"
           :use (:instance least-repeated-square-equiv-2 (tt tt) (m e) (p p))
           :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square))
           :do-not-induct t
           ))
  )

;; (defthm t-s-aux-lemma-4
;;   (implies (and (< 2 p)
;;                 (rtl::primep p)
;;                 )
;;            (not (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) 0)))
;;   :hints (("Goal"
;;            :use (:instance posp-Q*2^S-n-is-even (n (- p 1)))
;;            ))
;;   )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm t-s-aux-lemma-3
    (implies (and (rtl::primep p)
                  (< 2 p)
                  (< 0 n)
                  (< n p)
                  (natp n))
             (EQUAL (MOD (* (EXPT N
                                  (+ 1/2
                                     (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
                            (EXPT N
                                  (+ 1/2
                                     (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))))
                         P)
                    (MOD (* N (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P)))))
                         P)))
    :hints (("Goal"
             :in-theory (e/d (acl2::not-evenp-when-oddp) ())
             ))
    )
  )

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))

  (local
   (defthm t-s-aux-lemma-1
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c))
              (equal (expt (expt a b) c)
                     (expt a (* b c))))
     )
   )
  
  (defthm T-S-aux-lemma2
    (implies (and (rtl::primep p)
                  (< 2 p)
                  (natp z)
                  (not (has-square-root? z p))
                  (> z 0)
                  (< z p))
             (EQUAL (MOD (EXPT (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
                               (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P))))))
                         P)
                    (+ -1 P)))
    :hints (("Goal"
             
             :use ((:instance q2s-is-correct (n (- p 1)))
                   (:instance T-S-aux-euler-criterion (n z) (p p))
;(:instance t-s-aux-lemma-4 (p p))
                   (:instance t-s-aux-lemma-1
                              (a z)
                              (b (MV-NTH 0 (Q*2^S (+ -1 P))))
                              (c (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                   )
             :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
             ))
    )
  )



;; (defthm t-s-aux-equiv
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (natp p)
;;                 (natp z)
;;                 (< 2 p)
;;                 (< z p)
;;                 (rtl::primep p)
;;                 (< n p)
;;                 (has-square-root? n p)
;;                 (not (has-square-root? z p))

;;            ;(if n not =0 (mod ts-aux^2 p) 
;;            (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
;;            (equal (mv-nth 1 (Q*2^S (- p 1))) S)
;;            (equal (acl2::mod-expt-fast z Q p) c)
;;            (equal (acl2::mod-expt-fast n Q p) tt)
;;            (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R))

;;            (equal 

;;            (let ((i (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                            (mv-nth 1 (Q*2^S (- p 1))) p)))
;;              (if (zp i)
;;                  (equal (mod (* (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                 (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)) p)
;;                                 (mod n p))
;;                (let ((b (expt (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                               (expt 2 (- (- (mv-nth 1 (Q*2^S (- p 1))) i) 1)))))
;;                  (let ((M2 i)
;;                        (c2 (mod (* b b) p))
;;                        (tt2 (mod (* (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p) b b) p))
;;                        (R2 (mod (* (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    b) p)))
;;                    (declare (ignore M2 c2))
;;                    (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;;   )







;; --------

;; (local
;;  (defthm T-S-aux-=
;;    (implies  (and (natp M)
;;                   (natp c)
;;                   (natp tt)
;;                   (natp R)
;;                   (natp p)
;;                   (< 2 p))
;;              (equal (T-S-aux M c tt R p)
;;                     (let ((i (least-repeated-square tt M p)))
;;                       (if (zp i)
;;                           R
;;                         (let ((b (expt c (expt 2 (- (- M i) 1)))))
;;                           (let ((M2 i)
;;                                 (c2 (mod (* b b) p))
;;                                 (tt2 (mod (* tt b b) p))
;;                                 (R2 (mod (* R b) p)))
;;                             (T-S-aux M2 c2 tt2 R2 p))))))
;;              )
;;    )
;;  )

;; (defthm t-s-aux-lemma
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (natp p)
;;                 (natp z)
;;                 (> z 0)
;;                 (< 2 p)
;;                 (< z p)
;;                 (rtl::primep p)
;;                 (< n p)
;;                 (has-square-root? n p)
;;                 (not (has-square-root? z p)))
;;            (equal (mod (* (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                    (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    p)
;;                           (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                    (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    p)
;;                           )
;;                        p)
;;                   (mod n p)))
;;   :hints (("Goal"
;;            :use (
;;                  ;; (:instance T-S-aux-=
;;                  ;;            (tt (acl2::mod-expt-fast n  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (M (mv-nth 1 (Q*2^S (- p 1))))
;;                  ;;            (p p)
;;                  ;;            (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (R (acl2::mod-expt-fast n (/ (+  (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                  ;;            )
;;                  ;(:instance  t-s-aux-lemma-1 (z 
;;                  ;(:instance q2s-is-correct (n (- p 1)))
;;                  ;(:instance posp-Q*2^S-n-is-even (n (- p 1)))
;;                  ;; (:instance t-s-aux-equiv
;;                  ;;            (n n)
;;                  ;;            (p p)
;;                  ;;            (z z)
;;                  ;;            (tt (acl2::mod-expt-fast n  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (e (mv-nth 1 (Q*2^S (- p 1))))
;;                  ;;            (x (mv-nth 1 (Q*2^S (- p 1))))
;;                  ;;            (c (acl2::mod-expt-fast z  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (R (acl2::mod-expt-fast n (/ (+  (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                  ;;            )
;;                  )
;;            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) (least-repeated-square))
;;            ))
;;   )

;; ---



;; (encapsulate
;;   ()
;;   (local (include-book "arithmetic-3/top" :dir :system))
;;   (defthmd t-s-aux-lemma-1
;;     (implies (and (integerp a)
;;                   (integerp b)
;;                   (integerp c))
;;              (equal (expt (expt a b) c)
;;                     (expt a (* b c))))
;;     )
;;   )

;; z^(Q*2^(S-1)) = Z^((Q*2^S)/2) = Z^(p-1)/2 = -1 mod p

;; (encapsulate
;;   ()
;;   (local (include-book "arithmetic-5/top" :dir :system))
;;   (defthm t-s-aux-lemma-2-1
;;     (implies (and (integerp a)
;;                   (integerp b)
;;                   (integerp c))
;;              (equal (expt a (* b (expt 2 (- c 1))))
;;                     (expt a (/ (* b (expt 2 c)) 2)))))
;;   )

;; ;(encapsulate
;;  ; ()
;; ; (local (include-book "arithmetic-5/top" :dir :system))
;; (skip-proofs
;;  (defthm t-s-aux-lemma-2
;;    (implies (and (rtl::primep p)
;;                  (< 2 p)
;;                  (natp z)
;;                  (> z 0)
;;                  (not (has-square-root? z p)))               
;;             (EQUAL (MOD (EXPT (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                               (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P))))))
;;                         P)
;;                    (+ -1 P)))
;;    ;; :hints (("Goal"
;;    ;;          :cases ((> z 0)
;;    ;;                  (= z 0))
;;    ;;          ))
;;    )
;;  )

;; (skip-proofs
;;  (defthm t-s-aux-lemma-3
;;    (implies (and (rtl::primep p)
;;                  (< 2 p)
;;                  (< 0 n)
;;                  (< n p)
;;                  (natp n))
;;             (EQUAL (MOD (* (EXPT N
;;                                  (+ 1/2
;;                                     (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;                            (EXPT N
;;                                  (+ 1/2
;;                                     (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))))
;;                         P)
;;                    (MOD (* N (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                         P)))
;;    )
;;  )

;; (skip-proofs
;;  (defthm T-S-aux-lemma4
;;    (IMPLIES
;;     (AND
;;      (< 0 (MV-NTH 1 (Q*2^S (+ -1 P))))
;;      (< 0
;;         (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                     P)
;;                                (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                P))
;;      (EQUAL
;;       (MOD
;;        (*
;;         N
;;         (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;              P)
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;        P)
;;       (MOD
;;        (*
;;         N (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;        P))
;;      (INTEGERP N)
;;      (<= 0 N)
;;      (< 0 N)
;;      (<= 0 P)
;;      (INTEGERP Z)
;;      (<= 0 Z)
;;      (< 0 Z)
;;      (< 2 P)
;;      (< Z P)
;;      (RTL::PRIMEP P)
;;      (< N P)
;;      (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;             1)
;;      (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                  1)))
;;     (EQUAL
;;      (MOD
;;       (*
;;        (T-S-AUX
;;         (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                     P)
;;                                (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                P)
;;         (MOD
;;          (*
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N
;;                 (+ 1/2
;;                    (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         P)
;;        (T-S-AUX
;;         (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                     P)
;;                                (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                P)
;;         (MOD
;;          (*
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N
;;                 (+ 1/2
;;                    (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         P))
;;       P)
;;      N))
;;    )
;;  )

;; (skip-proofs
;;  (defthm t-s-aux-lemma-5
;;   (not (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) 0))))

;; (defthm t-s-aux-lemma
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (natp p)
;;                 (natp z)
;;                 (> z 0)
;;                 (< 2 p)
;;                 (< z p)
;;                 (rtl::primep p)
;;                 (< n p)
;;                 (has-square-root? n p)
;;                 (not (has-square-root? z p)))
;;            (equal (mod (* (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                    (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    p)
;;                           (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                    (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    p)
;;                           )
;;                        p)
;;                   (mod n p)))
;;   :hints (("Goal"
;;            :use (
;; ;(:instance T-s-aux-r2 (n n) (p p) (z z))
;;                  ;; (:instance T-S-aux-=
;;                  ;;            (tt (acl2::mod-expt-fast n  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (M (mv-nth 1 (Q*2^S (- p 1))))
;;                  ;;            (p p)
;;                  ;;            (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (R (acl2::mod-expt-fast n (/ (+  (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                  ;;            )
;;                  ;(:instance  t-s-aux-lemma-1 (z 
;;                  ;(:instance q2s-is-correct (n (- p 1)))
;;                  ;(:instance posp-Q*2^S-n-is-even (n (- p 1)))
;;                  (:instance t-s-aux-equiv
;;                             (n n)
;;                             (p p)
;;                             (z z)
;;                             (tt (acl2::mod-expt-fast n  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                             (e (mv-nth 1 (Q*2^S (- p 1))))
;;                             (x (mv-nth 1 (Q*2^S (- p 1))))
;;                             (c (acl2::mod-expt-fast z  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                             (R (acl2::mod-expt-fast n (/ (+  (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                             )
;;                  )
;;            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) (least-repeated-square))
;;            ))
;;   )



;; ;; (defthm T-s-aux-r2
;; ;;   (implies (and (natp n)
;; ;;                 (< 0 n)
;; ;;                 (natp p)
;; ;;                 (natp z)
;; ;;                 (< 2 p)
;; ;;                 (< z p)
;; ;;                 (rtl::primep p)
;; ;;                 (< n p)
;; ;;                 (has-square-root? n p)
;; ;;                 (not (has-square-root? z p)))
;; ;;            (mv-let (Q S)
;; ;;              (Q*2^S (- p 1))
;; ;;              (let (
;; ;;                    (M S)
;; ;;                    (c (acl2::mod-expt-fast z Q p))
;; ;;                    (tt (acl2::mod-expt-fast n Q p))
;; ;;                    (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
;; ;;                (declare (ignore c))
;; ;;                (let ((m1 (least-repeated-square tt M p)))
;; ;;                  (if (zp m1)
;; ;;                      (equal (mod (* R R) p) (mod n p))
;; ;;                    (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;; ;;   :hints (("Goal"
;; ;;            :use (
;; ;;                  (:instance t-s-aux-equiv
;; ;;                             (n n)
;; ;;                             (p p)
;; ;;                             (z z)
;; ;;                             (tt (acl2::mod-expt-fast n Q p))
;; ;;                             (e (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                             (x (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                             (c (acl2::mod-expt-fast z Q p))
;; ;;                             (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p))

;; ;;                             )
;; ;;                  )
;; ;;            :in-theory (e/d (acl2::mod-expt-fast) ())
;; ;;            ))
;; ;;   )

;; ;; (local
;; ;;  (defthm T-S-aux-=
;; ;;    (implies  (and (natp M)
;; ;;                   (natp c)
;; ;;                   (natp tt)
;; ;;                   (natp R)
;; ;;                   (natp p)
;; ;;                   (< 2 p))
;; ;;              (equal (T-S-aux M c tt R p)
;; ;;                     (let ((i (least-repeated-square tt M p)))
;; ;;                       (if (zp i)
;; ;;                           R
;; ;;                         (let ((b (expt c (expt 2 (- (- M i) 1)))))
;; ;;                           (let ((M2 i)
;; ;;                                 (c2 (mod (* b b) p))
;; ;;                                 (tt2 (mod (* tt b b) p))
;; ;;                                 (R2 (mod (* R b) p)))
;; ;;                             (T-S-aux M2 c2 tt2 R2 p))))))
;; ;;              )
;; ;;    )
;; ;;  )

;; ;; use defrule
;; ;; (encapsulate
;; ;;   ()
;; ;;   (local (include-book "arithmetic-3/top" :dir :system))
;; ;;   (defthmd t-s-aux-lemma-1
;; ;;     (implies (and (integerp a)
;; ;;                   (integerp b)
;; ;;                   (integerp c))
;; ;;              (equal (expt (expt a b) c)
;; ;;                     (expt a (* b c))))
;; ;;     )
;; ;;   )

;; ;z^(Q*2^(S-1)) = Z^((Q*2^S)/2) = Z^(p-1)/2 = -1 mod p

;; ;; (encapsulate
;; ;;   ()
;; ;;   (local (include-book "arithmetic-5/top" :dir :system))
;; ;;   (defthm t-s-aux-lemma-2-1
;; ;;     (implies (and (integerp a)
;; ;;                   (integerp b)
;; ;;                   (integerp c))
;; ;;              (equal (expt a (* b (expt 2 (- c 1))))
;; ;;                     (expt a (/ (* b (expt 2 c)) 2)))))
;; ;;   )

;; ;(encapsulate
;;  ; ()
;; ; (local (include-book "arithmetic-5/top" :dir :system))
;; (skip-proofs
;;  (defthm t-s-aux-lemma-2
;;    (implies (and (rtl::primep p)
;;                  (< 2 p)
;;                  (natp z)
;;                  (not (has-square-root? z p)))               
;;             (EQUAL (MOD (EXPT (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                               (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P))))))
;;                         P)
;;                    (+ -1 P)))
;;    ;; :hints (("Goal"
;;    ;;          :cases ((> z 0)
;;    ;;                  (= z 0))
;;    ;;          ))
;;    )
;;  )

;; (skip-proofs
;;  (defthm t-s-aux-lemma-3
;;    (implies (and (rtl::primep p)
;;                  (< 2 p)
;;                  (< 0 n)
;;                  (< n p)
;;                  (natp n))
;;             (EQUAL (MOD (* (EXPT N
;;                                  (+ 1/2
;;                                     (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;                            (EXPT N
;;                                  (+ 1/2
;;                                     (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))))
;;                         P)
;;                    (MOD (* N (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                         P)))
;;    )
;;  )

;; (skip-proofs
;;  (defthm T-S-aux-lemma4
;;    (IMPLIES
;;     (AND
;;      (< 0 (MV-NTH 1 (Q*2^S (+ -1 P))))
;;      (< 0
;;         (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                     P)
;;                                (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                P))
;;      (EQUAL
;;       (MOD
;;        (*
;;         N
;;         (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;              P)
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;        P)
;;       (MOD
;;        (*
;;         N (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;         (EXPT
;;          (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;               P)
;;          (EXPT
;;           2
;;           (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;        P))
;;      (INTEGERP N)
;;      (<= 0 N)
;;      (< 0 N)
;;      (<= 0 P)
;;      (INTEGERP Z)
;;      (<= 0 Z)
;;      (< 0 Z)
;;      (< 2 P)
;;      (< Z P)
;;      (RTL::PRIMEP P)
;;      (< N P)
;;      (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;             1)
;;      (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                  1)))
;;     (EQUAL
;;      (MOD
;;       (*
;;        (T-S-AUX
;;         (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                     P)
;;                                (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                P)
;;         (MOD
;;          (*
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N
;;                 (+ 1/2
;;                    (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         P)
;;        (T-S-AUX
;;         (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                     P)
;;                                (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                P)
;;         (MOD
;;          (*
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P)))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         (MOD
;;          (*
;;           (EXPT N
;;                 (+ 1/2
;;                    (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;           (EXPT
;;            (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                 P)
;;            (EXPT
;;             2
;;             (+
;;              -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;              (- (LEAST-REPEATED-SQUARE (MOD (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P))))
;;                                             P)
;;                                        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                                        P))))))
;;          P)
;;         P))
;;       P)
;;      N))
;;    )
;;  )

;; (skip-proofs
;;  (defthm t-s-aux-lemma-5
;;   (not (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) 0))))

;; (defthm t-s-aux-lemma
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (natp p)
;;                 (natp z)
;;                 (> z 0)
;;                 (< 2 p)
;;                 (< z p)
;;                 (rtl::primep p)
;;                 (< n p)
;;                 (has-square-root? n p)
;;                 (not (has-square-root? z p)))
;;            (equal (mod (* (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                    (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    p)
;;                           (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                    (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                    (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                    p)
;;                           )
;;                        p)
;;                   (mod n p)))
;;   :hints (("Goal"
;;            :use (
;; ;(:instance T-s-aux-r2 (n n) (p p) (z z))
;;                  ;; (:instance T-S-aux-=
;;                  ;;            (tt (acl2::mod-expt-fast n  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (M (mv-nth 1 (Q*2^S (- p 1))))
;;                  ;;            (p p)
;;                  ;;            (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
;;                  ;;            (R (acl2::mod-expt-fast n (/ (+  (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                  ;;            )
;;                  ;(:instance  t-s-aux-lemma-1 (z 
;;                  ;(:instance q2s-is-correct (n (- p 1)))
;;                  (:instance posp-Q*2^S-n-is-even (n (- p 1)))
;;                  (:instance t-s-aux-equiv
;;                             (n n)
;;                             (p p)
;;                             (z z)
;;                             (tt (acl2::mod-expt-fast n  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                             (e (mv-nth 1 (Q*2^S (- p 1))))
;;                             (x (mv-nth 1 (Q*2^S (- p 1))))
;;                             (c (acl2::mod-expt-fast z  (mv-nth 0 (Q*2^S (- p 1))) p))
;;                             (R (acl2::mod-expt-fast n (/ (+  (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                             )
;;                  )
;;            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) (least-repeated-square))
;;            ))
;;   )



;; ;; (defthm T-S-aux-gen
;; ;;   (implies (and (natp tt) ;; n^Q
;; ;;                 (rtl::primep p)
;; ;;                 (< 2 p)
;; ;;                 (< 0 e)
;; ;;                 (natp e) ;; e = S
;; ;;                 (equal m (least-repeated-square tt e p))
;; ;;                 (natp x);; x = S
;; ;;                 (equal (mod (expt c (expt 2 (- x 1))) p) -1) ;; c = quad-non-residue
;; ;;                 (integerp n)
;; ;;                 (integerp R) ;;R=(n^(Q+1/2))
;; ;;                 (integerp c)
;; ;;                 (equal (mod (* R R) p) (mod (* tt n) p)))
;; ;;            (if (zp m)
;; ;;                (equal (mod (* R R) p) (mod n p))
;; ;;              (let ((b (expt c (expt 2 (- (- e m) 1)))))
;; ;;                (let ((M2 m)
;; ;;                      (c2 (mod (* b b) p))
;; ;;                      (tt2 (mod (* tt b b) p))
;; ;;                      (R2 (mod (* R b) p)))
;; ;;                  (and (natp tt2)
;; ;;                       (rtl::primep p)
;; ;;                       (< 2 p)
;; ;;                       (< 0 m2)
;; ;;                       (natp M2)
;; ;;                       (natp x)
;; ;;                       (equal (mod (expt c (expt 2 (- x 1))) p) -1)
;; ;;                       (integerp n)
;; ;;                       (integerp R2)
;; ;;                       (integerp c2)
;; ;;                       (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;; ;;   :hints (("Goal"
;; ;;            :in-theory (disable least-repeated-square)
;; ;;            ))
;; ;;   )




;; ;; ;; (defthm t-s-aux-equiv
;; ;; ;;   (implies (and (natp n)
;; ;; ;;                 (< 0 n)
;; ;; ;;                 (natp p)
;; ;; ;;                 (natp z)
;; ;; ;;                 (< 2 p)
;; ;; ;;                 (< z p)
;; ;; ;;                 (rtl::primep p)
;; ;; ;;                 (< n p)
;; ;; ;;                 (has-square-root? n p)
;; ;; ;;                 (not (has-square-root? z p)))
;; ;; ;;                 ;; (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
;; ;; ;;                 ;; (equal (mv-nth 1 (Q*2^S (- p 1))) S)
;; ;; ;;                 ;; (equal (acl2::mod-expt-fast z Q p) c)
;; ;; ;;                 ;; (equal (acl2::mod-expt-fast n Q p) tt)
;; ;; ;;                 ;; (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R))
;; ;; ;;            (let ((i (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;; ;; ;;                                            (mv-nth 1 (Q*2^S (- p 1))) p)))
;; ;; ;;              (if (zp i)
;; ;; ;;                  (equal (mod (* (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;; ;; ;;                                 (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)) p)
;; ;; ;;                                 (mod n p))
;; ;; ;;                (let ((b (expt (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;; ;; ;;                               (expt 2 (- (- (mv-nth 1 (Q*2^S (- p 1))) i) 1)))))
;; ;; ;;                  (let ((M2 i)
;; ;; ;;                        (c2 (mod (* b b) p))
;; ;; ;;                        (tt2 (mod (* (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p) b b) p))
;; ;; ;;                        (R2 (mod (* (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;; ;; ;;                                    b) p)))
;; ;; ;;                    (declare (ignore M2 c2))
;; ;; ;;                    (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;; ;; ;;   )

;; ;; (defthm t-s-aux-equiv
;; ;;   (implies (and (natp n)
;; ;;                 (< 0 n)
;; ;; ;(natp p)
;; ;;                 (natp z)
;; ;; ;(< 2 p)
;; ;;                 (< z p)
;; ;; ;(rtl::primep p)
;; ;;                 (< n p)
;; ;;                 (has-square-root? n p)
;; ;;                 (not (has-square-root? z p))

;; ;;                 (natp tt) ;; n^Q
;; ;;                 (rtl::primep p)
;; ;;                 (< 2 p)
;; ;;                 (< 0 e)
;; ;;                 (natp e) ;; e = S
;; ;;                 (equal (least-repeated-square tt e p) m)
;; ;;                 (integerp c)
;; ;;                 (natp x);; x = S
;; ;;                 (equal (mod (expt c (expt 2 (- x 1))) p) -1) ;; c = quad-non-residue
;; ;; ;(integerp n)
;; ;;                 (integerp R) ;;R=(n^(Q+1/2))
;; ;; ;(integerp c)
;; ;;                 (equal (mod (* R R) p) (mod (* tt n) p)))
;; ;;            (if (= m 0)
;; ;;                (equal (mod (* R R) p) (mod n p))
;; ;;              (let ((b (expt c (expt 2 (- (- e m) 1)))))
;; ;;                (let ((M2 m)
;; ;;                      (c2 (mod (* b b) p))
;; ;;                      (tt2 (mod (* tt b b) p))
;; ;;                      (R2 (mod (* R b) p)))
;; ;;                  (and (natp tt2)
;; ;;                       (rtl::primep p)
;; ;;                       (< 2 p)
;; ;;                       (< 0 m2)
;; ;;                       (natp M2)
;; ;;                       (natp x)
;; ;;                       (equal (mod (expt c (expt 2 (- x 1))) p) -1)
;; ;; ;(integerp n)
;; ;;                       (integerp R2)
;; ;;                       (integerp c2)
;; ;;                       (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;; ;;   )


;; ;; (natp (acl2::mod-expt-fast n Q p)) ;; n^Q
;; ;; ;(< 2 p)
;; ;; ;(< 0 e)
;; ;; (natp (mv-nth 1 (Q*2^S (- p 1)))) ;; e = S
;; ;; (equal m (least-repeated-square tt e p))
;; ;; (natp (mv-nth 1 (Q*2^S (- p 1))));; x = S
;; ;; (equal (mod (expt c (expt 2 (- x 1))) p) -1) ;; c = quad-non-residue
;; ;; (integerp n)
;; ;; (integerp R) ;;R=(n^(Q+1/2))
;; ;; (integerp c)
;; ;; (equal (mod (* R R) p) (mod (* tt n) p)))

;; ;; ;; (skip-proofs
;; ;; ;;  (defthm least-repeated-square-equiv-3
;; ;; ;;    (implies  (and (natp tt)
;; ;; ;;                   (natp m)
;; ;; ;;                   (natp p)
;; ;; ;;                   (< 2 p)
;; ;; ;;                   (equal (least-repeated-square tt m p) lrs)
;; ;; ;;                   (<= 0 lrs1)
;; ;; ;;                   (< lrs1 lrs))
;; ;; ;;              (not (= (mod (expt tt (expt 2 lrs1)) p) 1)))))


;; ;; ;;   (local (include-book "rtl/rel11/lib/basic" :dir :system))
;; ;; ;; (local (include-book "arithmetic/expt" :dir :system))

;; ;; ;; (defthm T-S-aux-equiv
;; ;; ;;   (implies (and (natp tt) ;; n^Q
;; ;; ;;                 (rtl::primep p)
;; ;; ;;                 (< 2 p)
;; ;; ;; ;(equal Q (mv-nth 0 (Q*2^S (- p 1))))
;; ;; ;; ;(equal S (mv-nth 1 (Q*2^S (- p 1))))
;; ;; ;;                 (< 0 e)
;; ;; ;;                 (natp e) ;; e = S
;; ;; ;;                 (equal (least-repeated-square tt e p) m)
;; ;; ;;                 (natp x);; x = S
;; ;; ;;                 (equal (mod (expt c (expt 2 (- x 1))) p) -1) ;; c = quad-non-residue
;; ;; ;; ;(< m e)
;; ;; ;;                 (integerp n)
;; ;; ;;                 (integerp R) ;;R=(n^(Q+1/2))
;; ;; ;;                 (equal (mod (* R R) p) (mod (* tt n) p)))
;; ;; ;;            (integerp (EXPT C (EXPT 2 (+ -1 E (- (LEAST-REPEATED-SQUARE TT E
;; ;; ;;                                                                        P)))))))
;; ;; ;;   :hints (("Goal"
;; ;; ;;            :use ((:instance acl2::expt-type-prescription-integerp
;; ;; ;;                            (r 2)
;; ;; ;;                            (i (+ -1 E (- (LEAST-REPEATED-SQUARE TT E P)))))
;; ;; ;;                  (:instance acl2::expt-type-prescription-integerp
;; ;; ;;            ))
;; ;; ;;   )


;; ;; (defthm T-S-aux-gen
;; ;;   (implies (and (natp tt) ;; n^Q
;; ;;                 (rtl::primep p)
;; ;;                 (< 2 p)
;; ;;                 (< 0 e)
;; ;;                 (natp e) ;; e = S
;; ;;                 (equal m (least-repeated-square tt e p))
;; ;;                 (natp x);; x = S
;; ;;                 (equal (mod (expt c (expt 2 (- x 1))) p) -1) ;; c = quad-non-residue
;; ;;                 (integerp n)
;; ;;                 (integerp R) ;;R=(n^(Q+1/2))
;; ;;                 (integerp c)
;; ;;                 (equal (mod (* R R) p) (mod (* tt n) p)))
;; ;;            (if (zp m)
;; ;;                (equal (mod (* R R) p) (mod n p))
;; ;;              (let ((b (expt c (expt 2 (- (- e m) 1)))))
;; ;;                (let ((M2 m)
;; ;;                      (c2 (mod (* b b) p))
;; ;;                      (tt2 (mod (* tt b b) p))
;; ;;                      (R2 (mod (* R b) p)))
;; ;;                  (and (natp tt2)
;; ;;                       (rtl::primep p)
;; ;;                       (< 2 p)
;; ;;                       (< 0 m2)
;; ;;                       (natp M2)
;; ;;                       (natp x)
;; ;;                       (equal (mod (expt c (expt 2 (- x 1))) p) -1)
;; ;;                       (integerp n)
;; ;;                       (integerp R2)
;; ;;                       (integerp c2)
;; ;;                       (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;; ;;   :hints (("Goal"
;; ;;            :in-theory (disable least-repeated-square)
;; ;;            ))
;; ;;   )

;; ;; ;; (defthm posp-Q*2^S-n-is-even
;; ;; ;;   (implies (and (> n 1)
;; ;; ;;                 (natp n)
;; ;; ;;                 (evenp n))
;; ;; ;;            (posp (mv-nth 1 (Q*2^S n))))
;; ;; ;;   :hints (("Goal"
;; ;; ;;            :use ((:instance q2s-is-correct (n n))
;; ;; ;;                  (:instance q2s-q-is-odd (n n)))
;; ;; ;;            ))
;; ;; ;;   )

;; ;; (defthm  t-s-aux-equiv-lemma1
;; ;;   (implies (and (natp n)
;; ;;                 (< 0 n)
;; ;;                 (natp p)
;; ;;                 (natp z)
;; ;;                 (< 2 p)
;; ;;                 (< z p)
;; ;;                 (rtl::primep p)
;; ;;                 (< n p)
;; ;;                 (has-square-root? n p)
;; ;;                 (not (has-square-root? z p)))
;; ;;            (NATP (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P))) P))))

;; ;; (defthm t-s-aux-equiv
;; ;;   (implies (and (natp n)
;; ;;                 (< 0 n)
;; ;;                 (natp p)
;; ;;                 (natp z)
;; ;;                 (< 2 p)
;; ;;                 (< z p)
;; ;;                 (rtl::primep p)
;; ;;                 (< n p)
;; ;;                 (has-square-root? n p)
;; ;;                 (not (has-square-root? z p)))
;; ;;            ;; (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
;; ;;            ;; (equal (mv-nth 1 (Q*2^S (- p 1))) S)
;; ;;            ;; (equal (acl2::mod-expt-fast z Q p) c)
;; ;;            ;; (equal (acl2::mod-expt-fast n Q p) tt)
;; ;;            ;; (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R))
;; ;;            (let ((i (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;; ;;                                            (mv-nth 1 (Q*2^S (- p 1))) p)))
;; ;;              (if (zp i)
;; ;;                  (equal (mod (* (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;; ;;                                 (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)) p)
;; ;;                         (mod n p))
;; ;;                (let ((b (expt (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;; ;;                               (expt 2 (- (- (mv-nth 1 (Q*2^S (- p 1))) i) 1)))))
;; ;;                  (let ((M2 i)
;; ;;                        (c2 (mod (* b b) p))
;; ;;                        (tt2 (mod (* (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p) b b) p))
;; ;;                        (R2 (mod (* (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;; ;;                                    b) p)))
;; ;;                    (declare (ignore M2 c2))
;; ;;                    (equal (mod (* R2 R2) p) (mod (* tt2 n) p)))))))
;; ;;   )
;; ;; :hints (("Goal"
;; ;;          :use (
;; ;;                ;; (:instance T-S-aux-gen
;; ;;                ;;           (tt (acl2::mod-expt-fast n Q p))
;; ;;                ;;           (p p)
;; ;;                ;;           (c (acl2::mod-expt-fast z Q p))
;; ;;                ;;           (e (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                ;;           (x (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                ;;           (n n)
;; ;;                ;;           (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p))
;; ;;                ;;           (m (least-repeated-square tt S p))
;; ;;                ;;           )
;; ;;                )
;; ;; ;(:instance posp-Q*2^S-n-is-even (n (- p 1))))
;; ;;          :in-theory (e/d (acl2::mod-expt-fast) (least-repeated-square))
;; ;;          )

;; ;;         ("Subgoal 2"
;; ;;          :use (
;; ;;                (:instance T-S-aux-gen
;; ;;                           (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
;; ;;                           (p p)
;; ;;                           (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
;; ;;                           (e (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                           (x (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                           (n n)
;; ;;                           (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;; ;; ;(m (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1)))
;; ;; ;                                              p)
;; ;; ;                        (mv-nth 1 (Q*2^S (- p 1))) p))
;; ;;                           )
;; ;;                (:instance t-s-aux-equiv-lemma1 (n n) (p p))
;; ;;                )
;; ;; ;:in-theory nil
;; ;;          )
;; ;;         )
;; ;; )



;; ;; (defthm T-s-aux-r2
;; ;;   (implies (and (natp n)
;; ;;                 (natp p)
;; ;;                 (natp z)
;; ;;                 (< 2 p)
;; ;;                 (< z p)
;; ;;                 (rtl::primep p)
;; ;;                 (< n p)
;; ;;                 (has-square-root? n p)
;; ;;                 (not (has-square-root? z p)))
;; ;;            (mv-let (Q S)
;; ;;              (Q*2^S (- p 1))
;; ;;              (let (
;; ;;                    (M S)
;; ;;                    (c (acl2::mod-expt-fast z Q p))
;; ;;                    (tt (acl2::mod-expt-fast n Q p))
;; ;;                    (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
;; ;;                (declare (ignore M c))
;; ;;                (equal (mod (* R R) p) (mod (* tt n) p)))))
;; ;;   :hints (("Goal"
;; ;;            :in-theory nil
;; ;;            ))
;; ;;   )
;; ;; :hints (("Goal"
;; ;;          :cases ((= n 0)
;; ;;                  (>= N 1))
;; ;;          :in-theory (e/d (ACL2::MOD-EXPT-FAST expt rtl::primep natp acl2::not-evenp-when-oddp) (mv-nth)) 
;; ;;          ))
;; ;; )
;; ;; ;;   )





;; ;; (mv-let (Q S) (Q*2^S (- p 1))
;; ;;   (let ((M S)
;; ;;         (c (acl2::mod-expt-fast z Q p))
;; ;;         (tt (acl2::mod-expt-fast n Q p))
;; ;;         (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
;; ;;     (declare (ignore M c)
;; ;;              (let ((i (least-repeated-square tt M p)))
;; ;;                (if (zp i)
;; ;;                    (equal (mod (* R R) p) (mod n p))
;; ;;                  (equal (mod (* R R) p) (mod (* tt2 n) p)))))))
;; ;; )


;; ;; ;(natp M)
;; ;; ;   (natp c)
;; ;; ;  (natp tt)
;; ;; ; (natp R)
;; ;; (natp z)
;; ;; (natp p)
;; ;; (< 2 p)
;; ;; (< 0 n)
;; ;; ; has sqr roott n
;; ;; (< n p)
;; ;; (has-square-root? n p)
;; ;; (not (has-square-root? z p))
;; ;; (< z p)          
;; ;; (integerp n)
;; ;; (rtl::primep p)
;; ;; (equal Q (mv-nth 0 (Q*2^S (- p 1))))
;; ;; (equal S (mv-nth 1 (Q*2^S (- p 1))))
;; ;; ;(equal M S)
;; ;; ;(equal c (acl2::mod-expt-fast z Q p))
;; ;; ;(equal tt (acl2::mod-expt-fast n Q p))
;; ;; (equal R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
;; ;; ;(equal (mod (* R R) p) (mod (* (acl2::mod-expt-fast n Q p) n) p)))




;; ;; (local
;; ;;  (defthm T-S-aux-=
;; ;;    (implies  (and (natp M)
;; ;;                   (natp c)
;; ;;                   (natp tt)
;; ;;                   (natp R)
;; ;;                   (natp p)
;; ;;                   (< 2 p))
;; ;;              (equal (T-S-aux M c tt R p)
;; ;;                     (let ((i (least-repeated-square tt M p)))
;; ;;                       (if (zp i)
;; ;;                           R
;; ;;                         (let ((b (expt c (expt 2 (- (- M i) 1)))))
;; ;;                           (let ((M2 i)
;; ;;                                 (c2 (mod (* b b) p))
;; ;;                                 (tt2 (mod (* tt b b) p))
;; ;;                                 (R2 (mod (* R b) p)))
;; ;;                             (T-S-aux M2 c2 tt2 R2 p))))))
;; ;;              )
;; ;;    )
;; ;;  )





;; ;; (defthm least-repeated-square
;; ;;   (implies (and (integerp r)
;; ;;                 (> r 0)
;; ;;                 (posp b)
;; ;;                 (= (mod (expt b (expt 2 r)) p) 1)
;; ;;                 ;; (<= 0 m)
;; ;;                 ;; (< m r)

;; ;;                 )
;; ;;            (let (m (least-repeated-square b r p))
;; ;;              (= (mod (expt b (expt 2 m)) p) 1))))













































































































;; ;; (defthm t-s-aux-lemma
;; ;;   (implies  (and (natp z)
;; ;;                  (natp p)
;; ;;                  (< 2 p)
;; ;;                  (< 0 n)
;; ;;                  (< n p)
;; ;;                  (has-square-root? n p)
;; ;;                  (not (has-square-root? z p))
;; ;;                  (< z p)          
;; ;;                  (natp n)
;; ;;                  (rtl::primep p))
;; ;;             (equal (mod (* (T-S-aux S
;; ;;                                     (acl2::mod-expt-fast z Q p)
;; ;;                                     (acl2::mod-expt-fast n Q p) R p)
;; ;;                            (T-S-aux S
;; ;;                                     (acl2::mod-expt-fast z Q p)
;; ;;                                     (acl2::mod-expt-fast n Q p) R p)) p)
;; ;;                    (mod n p)))
;; ;;   :hints (("Goal"
;; ;;            :in-theory (disable least-repeated-square)
;; ;;            )

;; ;;           ("Subgoal *1/2.3"
;; ;;            :in-theory (disable least-repeated-square)
;; ;;            )

;;           )
;;   )







;; (IMPLIES
;;  (AND
;;   (<
;;    0
;;    (LEAST-REPEATED-SQUARE (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                                P)
;;                           (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                           P))
;;   (EQUAL
;;    (MOD
;;     (*
;;      (T-S-AUX
;;       (LEAST-REPEATED-SQUARE
;;        (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                             P)
;;        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;        P)
;;       (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                            P)
;;       (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                            P)
;;       (MOD
;;        (*
;;         (ACL2::MOD-EXPT-FAST N
;;                              (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                              P)
;;         (EXPT
;;          (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                               P)
;;          (EXPT 2
;;                (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                   (- (LEAST-REPEATED-SQUARE
;;                       (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                            P)
;;                       (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                       P))))))
;;        P)
;;       P)
;;      (T-S-AUX
;;       (LEAST-REPEATED-SQUARE
;;        (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                             P)
;;        (MV-NTH 1 (Q*2^S (+ -1 P)))
;;        P)
;;       (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                            P)
;;       (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                            P)
;;       (MOD
;;        (*
;;         (ACL2::MOD-EXPT-FAST N
;;                              (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                              P)
;;         (EXPT
;;          (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                               P)
;;          (EXPT 2
;;                (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                   (- (LEAST-REPEATED-SQUARE
;;                       (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                            P)
;;                       (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                       P))))))
;;        P)
;;       P))
;;     P)
;;    N)
;;   (INTEGERP Z)
;;   (<= 0 Z)
;;   (<= 0 P)
;;   (< 2 P)
;;   (< 0 N)
;;   (< N P)
;;   (INTEGERP N)
;;   (<= 0 N)
;;   (ODDP P)
;;   (EQUAL (ACL2::MOD-EXPT-FAST N (+ -1/2 (* 1/2 P))
;;                               P)
;;          1)
;;   (NOT (EQUAL (ACL2::MOD-EXPT-FAST Z (+ -1/2 (* 1/2 P))
;;                                    P)
;;               1))
;;   (< Z P)
;;   (RTL::PRIMEP P))
;;  (EQUAL
;;   (MOD
;;    (*
;;     (T-S-AUX
;;      (LEAST-REPEATED-SQUARE
;;       (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                            P)
;;       (MV-NTH 1 (Q*2^S (+ -1 P)))
;;       P)
;;      (MOD
;;       (*
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P)))))
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P))))))
;;       P)
;;      (MOD
;;       (*
;;        (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                             P)
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P)))))
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P))))))
;;       P)
;;      (MOD
;;       (*
;;        (ACL2::MOD-EXPT-FAST N
;;                             (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                             P)
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P))))))
;;       P)
;;      P)
;;     (T-S-AUX
;;      (LEAST-REPEATED-SQUARE
;;       (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                            P)
;;       (MV-NTH 1 (Q*2^S (+ -1 P)))
;;       P)
;;      (MOD
;;       (*
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P)))))
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P))))))
;;       P)
;;      (MOD
;;       (*
;;        (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                             P)
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P)))))
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P))))))
;;       P)
;;      (MOD
;;       (*
;;        (ACL2::MOD-EXPT-FAST N
;;                             (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                             P)
;;        (EXPT
;;         (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                              P)
;;         (EXPT 2
;;               (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                  (- (LEAST-REPEATED-SQUARE
;;                      (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;;                                           P)
;;                      (MV-NTH 1 (Q*2^S (+ -1 P)))
;;                      P))))))
;;       P)
;;      P))
;;    P)
;;   N))












































































;; (defthm test-lemma
;;   (IMPLIES
;;    (AND
;;     (NOT (ZP (LEAST-REPEATED-SQUARE TT M P)))
;;     (IMPLIES
;;      (AND
;;       (NATP (LEAST-REPEATED-SQUARE TT M P))
;;       (NATP
;;        (MOD (* (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P))
;;       (NATP
;;        (MOD (* TT
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P))
;;       (NATP
;;        (MOD (* R
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P))
;;       (NATP Z)
;;       (NATP P)
;;       (< 2 P)
;;       (< 0 N)
;;       (< N P)
;;       (NOT (HAS-SQUARE-ROOT? Z P))
;;       (< Z P)
;;       (INTEGERP N)
;;       (RTL::PRIMEP P)
;;       (EQUAL (MV-NTH 0 (Q*2^S (+ -1 P))) Q)
;;       (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) S)
;;       (EQUAL (LEAST-REPEATED-SQUARE TT M P) S)
;;       (EQUAL
;;        (MOD (* (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (ACL2::MOD-EXPT-FAST Z Q P))
;;       (EQUAL
;;        (MOD (* TT
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (ACL2::MOD-EXPT-FAST N Q P))
;;       (EQUAL
;;        (MOD (* R
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (ACL2::MOD-EXPT-FAST N (* (+ Q 1) 1/2)
;;                             P))
;;       (EQUAL
;;        (MOD
;;         (* (MOD (* R
;;                    (REPEATED-SQUARE C
;;                                     (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                     P))
;;                 P)
;;            (MOD (* R
;;                    (REPEATED-SQUARE C
;;                                     (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                     P))
;;                 P))
;;         P)
;;        (MOD
;;         (* (MOD (* TT
;;                    (REPEATED-SQUARE C
;;                                     (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                     P)
;;                    (REPEATED-SQUARE C
;;                                     (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                     P))
;;                 P)
;;            N)
;;         P)))
;;      (EQUAL
;;       (MOD
;;        (*
;;         (T-S-AUX
;;          (LEAST-REPEATED-SQUARE TT M P)
;;          (MOD (* (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P)
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          (MOD (* TT
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P)
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          (MOD (* R
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          P)
;;         (T-S-AUX
;;          (LEAST-REPEATED-SQUARE TT M P)
;;          (MOD (* (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P)
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          (MOD (* TT
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P)
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          (MOD (* R
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          P))
;;        P)
;;       (MOD N P))))
;;    (IMPLIES (AND (NATP M)
;;                  (NATP C)
;;                  (NATP TT)
;;                  (NATP R)
;;                  (NATP Z)
;;                  (NATP P)
;;                  (< 2 P)
;;                  (< 0 N)
;;                  (< N P)
;;                  (NOT (HAS-SQUARE-ROOT? Z P))
;;                  (< Z P)
;;                  (INTEGERP N)
;;                  (RTL::PRIMEP P)
;;                  (EQUAL (MV-NTH 0 (Q*2^S (+ -1 P))) Q)
;;                  (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) S)
;;                  (EQUAL M S)
;;                  (EQUAL C (ACL2::MOD-EXPT-FAST Z Q P))
;;                  (EQUAL TT (ACL2::MOD-EXPT-FAST N Q P))
;;                  (EQUAL R
;;                         (ACL2::MOD-EXPT-FAST N (* (+ Q 1) 1/2)
;;                                              P))
;;                  (EQUAL (MOD (* R R) P)
;;                         (MOD (* TT N) P)))
;;             (EQUAL (MOD (* (T-S-AUX M C TT R P)
;;                            (T-S-AUX M C TT R P))
;;                         P)
;;                    (MOD N P))))
;;   :hints (("Goal"
;;            :in-theory nil
;;            ))
;;   )



;; ;; (encapsulate
;; ;;   ()
;; ;;   (local (include-book "arithmetic-5/top" :dir :system))
;; ;;   (defthm T-s-aux-r2
;; ;;     (implies (and (natp n)
;; ;;                   (natp p)
;; ;;                   (natp z)
;; ;;                   (< 2 p)
;; ;;                   (< z p)
;; ;;                   (rtl::primep p)
;; ;;                   (< n p)
;; ;;                   (has-square-root? n p)
;; ;;                   (not (has-square-root? z p)))
;; ;;              (mv-let (Q S)
;; ;;                (Q*2^S (- p 1))
;; ;;                (let (
;; ;;                      (M S)
;; ;;                      (c (acl2::mod-expt-fast z Q p))
;; ;;                      (tt (acl2::mod-expt-fast n Q p))
;; ;;                      (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
;; ;;                  (declare (ignore M c))
;; ;;                  (equal (mod (* R R) p) (mod (* tt n) p)))))
;; ;;     :hints (("Goal"
;; ;;              :cases ((= n 0)
;; ;;                      (>= N 1))
;; ;;              :in-theory (e/d (ACL2::MOD-EXPT-FAST expt rtl::primep natp acl2::not-evenp-when-oddp) (mv-nth)) 
;; ;;              ))
;; ;;     )
;; ;;   )

;; ;; (defthm least-repeated-square-aux-=
;; ;;   (implies (and (natp i)
;; ;;                 ;(< i M)
;; ;;                 (natp tt^2^i)
;; ;;                 (natp M)
;; ;;                 (natp p)
;; ;;                 (< 2 p))
;; ;;            (equal (least-repeated-square-aux i tt^2^i M p)
;; ;;                   (if (not (and (< i M) (< 0 i)))
;; ;;                       0
;; ;;                     (if (= (mod (* tt^2^i tt^2^i) p) 1)
;; ;;                         i
;; ;;                       (least-repeated-square-aux (+ i 1) (mod (* tt^2^i tt^2^i) p) M p)))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            ))
;; ;;   )

;; ;; (defthm least-repeated-square-aux=
;; ;;   (IMPLIES (AND (INTEGERP TT)
;; ;;                 (<= 0 TT)
;; ;;                 (INTEGERP M)
;; ;;                 (<= 0 M)
;; ;;                 (INTEGERP P)
;; ;;                 (<= 0 P)
;; ;;                 (< 2 P)
;; ;;                 (< 1 M)
;; ;;                 (<= 3 P)
;; ;;                 (< 1 TT)
;; ;;                 (EQUAL (mod (EXPT TT (EXPT 2 i)) p) 1))
;; ;;            (Equal (LEAST-REPEATED-SQUARE-AUX 1 TT M P) i))
;; ;;   :hints (("Goal"
;; ;;            :in-theory (enable least-repeated-square-aux)
;; ;;            ))
;; ;;   )

;; ;; (skip-proofs
;; ;;  (defthm least-repeated-square-=
;; ;;    (implies (and (natp tt)
;; ;;                  (natp M)
;; ;;                  (natp p)
;; ;;                  (< 2 p)
;; ;;                  ;(< 0 tt)
;; ;;                  (equal (least-repeated-square tt M p) i))
;; ;;             (equal (mod (expt tt (expt 2 i)) p) 1))
;; ;;    :hints (("Goal"
;; ;;             :in-theory (enable least-repeated-square-aux expt)
;; ;;             ))
;; ;;    )
;; ;; )

;; ;; (defthm T-s-aux-m-=0-lemma1
;; ;;   (implies (and (natp n)
;; ;;                 (< 0 n)
;; ;;                 (rtl::primep p)
;; ;;                 (< n p)
;; ;;                 (natp q))
;; ;;            (not (equal (ACL2::MOD-EXPT-FAST N q p) 0))
;; ;;            )
;; ;;   :hints (("Goal"
;; ;; ;:use (:instance least-repeated-square-= (tt tt) (M M) (p p) (i 0))
;; ;;            :in-theory (enable acl2::mod-expt-fast)
;; ;;            ))
;; ;;   )

;; ;; (encapsulate
;; ;;   ()

;; ;;   (local (include-book "rtl/rel11/lib/basic" :dir :system))
;; ;;   (local (include-book "arithmetic/equalities" :dir :system))

;; ;;   (defthm expt-type-prescription-integerp-1
;; ;;         (implies (and (natp i) (natp r))
;; ;;                  (natp (expt r i)))
;; ;;         :rule-classes (:type-prescription :generalize))

;; ;; (defthm T-s-aux-m-=0-lemma1
;; ;;   (implies (and (natp n)
;; ;;                 (< 0 n)
;; ;;                 (< n p)
;; ;;                 (< 2 p)
;; ;;                 (natp p)
;; ;;                 (rtl::primep p)
;; ;;                 (equal Q (mv-nth 0 (Q*2^S (- p 1))))
;; ;;                 (equal (acl2::mod-expt-fast n Q p) tt))
;; ;;            ;(and (< 0 tt)
;; ;;            (integerp tt))
;; ;;   :hints (("Goal"
;; ;;            :in-theory (enable acl2::mod-expt-fast)
;; ;;            ))
;; ;;   )

;; ;; (defthm T-s-aux-m-=0
;; ;;   (implies (and (natp p)
;; ;;                 (< 2 p)
;; ;;                 (rtl::primep p)
;; ;;                 (natp tt)
;; ;;                 (equal S (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                 (equal M S)
;; ;;                 (equal (least-repeated-square tt M p) i)
;; ;;                 (equal i 0))
;; ;;            (equal (mod tt p) (mod 1 p)))
;; ;;   :hints (("Goal"
;; ;;            :use ((:instance least-repeated-square-= (tt tt) (M M) (p p) (i 0)))
;; ;;            ))
;; ;;   )

;; ;; (encapsulate
;; ;;   ()

;; ;;   (skip-proofs
;; ;;    (local
;; ;;     (defthm T-s-aux-m=0-subgoal2
;; ;;       (IMPLIES (AND (INTEGERP N)
;; ;;                     (<= 0 N)
;; ;;                     (<= 0 P)
;; ;;                     (INTEGERP Z)
;; ;;                     (<= 0 Z)
;; ;;                     (< 2 P)
;; ;;                     (< Z P)
;; ;;                     (RTL::PRIMEP P)
;; ;;                     (< N P)
;; ;;                     (ODDP P)
;; ;;                     (EQUAL (ACL2::MOD-EXPT-FAST N (+ -1/2 (* 1/2 P))
;; ;;                                                 P)
;; ;;                            1)
;; ;;                     (NOT (EQUAL (ACL2::MOD-EXPT-FAST Z (+ -1/2 (* 1/2 P))
;; ;;                                                      P)
;; ;;                                 1))
;; ;;                     (EQUAL (LEAST-REPEATED-SQUARE-AUX
;; ;;                             1
;; ;;                             (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;; ;;                                                  P)
;; ;;                             (MV-NTH 1 (Q*2^S (+ -1 P)))
;; ;;                             P)
;; ;;                            0))
;; ;;                (EQUAL (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;; ;;                                            P)
;; ;;                       1))
;; ;;       )
;; ;;     )
;; ;;    )

;; ;;   (skip-proofs
;; ;;    (local
;; ;;     (defthm T-s-aux-m=0-subgoal1
;; ;;       (IMPLIES (AND (INTEGERP N)
;; ;;                     (<= 0 N)
;; ;;                     (<= 0 P)
;; ;;                     (INTEGERP Z)
;; ;;                     (<= 0 Z)
;; ;;                     (< 2 P)
;; ;;                     (< Z P)
;; ;;                     (RTL::PRIMEP P)
;; ;;                     (< N P)
;; ;;                     (ODDP P)
;; ;;                     (EQUAL (ACL2::MOD-EXPT-FAST N (+ -1/2 (* 1/2 P))
;; ;;                                                 P)
;; ;;                            1)
;; ;;                     (NOT (EQUAL (ACL2::MOD-EXPT-FAST Z (+ -1/2 (* 1/2 P))
;; ;;                                                      P)
;; ;;                                 1))
;; ;;                     (<= (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;; ;;                                              P)
;; ;;                         1))
;; ;;                (EQUAL (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
;; ;;                                            P)
;; ;;                       1))
;; ;;       )
;; ;;     )
;; ;;    )

;; ;;   (defthm T-s-aux-loop-m-=0
;; ;;     (implies (and (natp n)
;; ;;                   (natp p)
;; ;;                   (natp z)
;; ;;                   (< 2 p)
;; ;;                   (< z p)
;; ;;                   (< 0 n)
;; ;;                   (rtl::primep p)
;; ;;                   (< n p)
;; ;;                   (has-square-root? n p)
;; ;;                   (not (has-square-root? z p))
;; ;;                   (equal Q (mv-nth 0 (Q*2^S (- p 1))))
;; ;;                   (equal S (mv-nth 1 (Q*2^S (- p 1))))
;; ;;                   (equal M S)
;; ;;                   (equal (acl2::mod-expt-fast z Q p) c)
;; ;;                   (equal (acl2::mod-expt-fast n Q p) tt)
;; ;;                   (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R)
;; ;;                   (equal (least-repeated-square tt M p) i)
;; ;;                   (equal i 0))
;; ;;              (equal (acl2::mod-expt-fast n Q p) 1)))
;; ;;   )

;; ;; (skip-proofs
;; ;;  (defthm T-S-aux-loop
;; ;;    (implies  (and (natp M)
;; ;;                   (natp c)
;; ;;                   (natp tt)
;; ;;                   (natp R)
;; ;;                   (natp p)
;; ;;                   (rtl::primep p)
;; ;;                   (integerp i)
;; ;;                   (< 2 p)
;; ;;                   (< 0 i)
;; ;;                   (< i M)
;; ;;                   (equal (repeated-square c (- (- M i) 1) p) b)
;; ;;                   (equal M2 i)
;; ;;                   (equal (mod (* b b) p) c2)
;; ;;                   (equal (mod (* tt b b) p) tt2)
;; ;;                   (equal (mod (* R b) p) R2)
;; ;;                   (equal (mod (* R R) p) (mod (* tt n) p)))
;; ;;              (equal (mod (* r2 r2) p) (mod (* tt2 n) p))))
;; ;;  )

;; ;; (defthm T-S-aux-loop-i=0
;; ;;   (implies  (and (natp M)
;; ;;                  (natp c)
;; ;;                  (natp tt)
;; ;;                  (natp R)
;; ;;                  (natp p)
;; ;;                  (integerp i)
;; ;;                  (rtl::primep p)
;; ;;                  (< 2 p)
;; ;;                  (< 0 i)
;; ;;                  (< i M)
;; ;;                  (equal (repeated-square c (- (- M i) 1) p) b)
;; ;;                  (equal M2 i)
;; ;;                  (equal (mod (* b b) p) c2)
;; ;;                  (equal (mod (* tt b b) p) tt2)
;; ;;                  (equal (mod (* R b) p) R2)
;; ;;                  (equal (least-repeated-square tt2 M2 p) 0)
;; ;;                  (equal (mod (* R R) p) (mod (* tt n) p)))
;; ;;             (equal (mod (* tt b b) p) 1)))

;; ;;                                      (let ((i (least-repeated-square tt M p)))
;; ;;                       (if (zp i)
;; ;;                           R
;; ;;                         (let ((b (repeated-square c (- (- M i) 1) p)))
;; ;;                           (let ((M2 i)
;; ;;                                 (c2 (mod (* b b) p))
;; ;;                                 (tt2 (mod (* tt b b) p))
;; ;;                                 (R2 (mod (* R b) p)))







;; (defthm tonelli-shanks-is-sqrt-modp
;;   (implies (and (natp p)
;;                 (> p 2)
;;                 (oddp p);; remove this
;;                 (rtl::primep p)
;;                 (fep n p)
;;                 (fep z p)
;;                 (not (has-square-root? z p))
;;                 (equal (tonelli-shanks-sqrt n p z) y))
;; ;(not (= y 0)))
;;            (= (mod (* y y) p) n))


;;   :hints (("Goal"
;; 	   :in-theory (e/d (tonelli-shanks-sqrt fep rtl::primep)
;;                            (least-repeated-square repeated-square Q*2^S t-s-aux))
;; 	   ))
;;   )
;; ("Subgoal 1"
;; ;:use (:instance
;;  :use ((:instance posp-Q*2^S-n-is-odd (n (- p 1))))
;; ;:in-theory (enable rtl::primep)
;;  )
;; )
;; )

;; ;; (defthm tonelli-shanks-is-correct
;; ;;   (implies (and (natp p)
;; ;;                 (> p 2)
;; ;;                 (rtl::primep p)
;; ;;                 (fep n p)
;; ;;                 (fep z p)
;; ;;                 (not (has-square-root? z p))
;; ;;                 (fep y p)
;; ;;                 (= (mod (* y y) p) n))
;; ;;            (or (= (tonelli-shanks-sqrt n p z) y)
;; ;;                (= (tonelli-shanks-sqrt n p z) (- p y)))))

;; ;; (defthm tonelli-shanks-is-sqrt-modp
;; ;;   (implies (and (natp n)
;; ;; 		(natp p)
;; ;; 		(natp z)
;; ;; 		(> p 2)
;; ;; 		(< z p)
;; ;; 		(rtl::primep p)
;; ;; 		(not (has-square-root? z p))
;; ;; 		(equal (tonelli-shanks-sqrt n p z) y)
;; ;; 		(not (= y 0)))
;; ;; 	   (= (mod (* y y) p) n))
;; ;;   )



;; ;; (defthm tonelli-shanks-is-correct
;; ;;   (implies (and (natp n)
;; ;; 		(natp p)
;; ;; 		(natp z)
;; ;; 		(> p 2)
;; ;; 		(< z p)
;; ;; 		(rtl::primep p)
;; ;; 		(not (has-square-root? z p))
;; ;; 		(not (= y 0))
;; ;; 		(= (mod (* y y) p) n))
;; ;; 	   (or (= (tonelli-shanks-sqrt n p z) y)
;; ;; 	       (= (tonelli-shanks-sqrt n p z) (- p y))))
;; ;;   )




;; (IMPLIES
;;  (AND
;;   (NOT (ZP (LEAST-REPEATED-SQUARE TT M P)))
;;   (IMPLIES
;;    (AND
;;     (NATP (LEAST-REPEATED-SQUARE TT M P))
;;     (NATP
;;      (MOD (* (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P)
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P))
;;           P))
;;     (NATP
;;      (MOD (* TT
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P)
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P))
;;           P))
;;     (NATP
;;      (MOD (* R
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P))
;;           P))
;;     (NATP P)
;;     (< 2 P)
;;     (< 0 N)
;;     (< N P)
;;     (INTEGERP N)
;;     (RTL::PRIMEP P)
;;     (EQUAL (MV-NTH 0 (Q*2^S (+ -1 P))) Q)
;;     (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) S)
;;     (EQUAL (LEAST-REPEATED-SQUARE TT M P) S)
;;     (EQUAL
;;      (MOD (* (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P)
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P))
;;           P)
;;      (ACL2::MOD-EXPT-FAST Z Q P))
;;     (EQUAL
;;      (MOD (* TT
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P)
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P))
;;           P)
;;      (ACL2::MOD-EXPT-FAST N Q P))
;;     (EQUAL
;;      (MOD (* R
;;              (REPEATED-SQUARE C
;;                               (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                               P))
;;           P)
;;      (ACL2::MOD-EXPT-FAST N (* (+ Q 1) 1/2)
;;                           P))
;;     (EQUAL
;;      (MOD
;;       (* (MOD (* R
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          (MOD (* R
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P))
;;       P)
;;      (MOD
;;       (* (MOD (* TT
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P)
;;                  (REPEATED-SQUARE C
;;                                   (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                   P))
;;               P)
;;          N)
;;       P)))





;;    (EQUAL
;;     (MOD
;;      (*
;;       (T-S-AUX
;;        (LEAST-REPEATED-SQUARE TT M P)
;;        (MOD (* (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (MOD (* TT
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (MOD (* R
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        P)
;;       (T-S-AUX
;;        (LEAST-REPEATED-SQUARE TT M P)
;;        (MOD (* (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (MOD (* TT
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P)
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        (MOD (* R
;;                (REPEATED-SQUARE C
;;                                 (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 P))
;;             P)
;;        P))
;;      P)
;;     (MOD N P))))
;;  (IMPLIES (AND (NATP M)
;;                (NATP C)
;;                (NATP TT)
;;                (NATP R)
;;                (NATP P)
;;                (< 2 P)
;;                (< 0 N)
;;                (< N P)
;;                (INTEGERP N)
;;                (RTL::PRIMEP P)
;;                (EQUAL (MV-NTH 0 (Q*2^S (+ -1 P))) Q)
;;                (EQUAL (MV-NTH 1 (Q*2^S (+ -1 P))) S)
;;                (EQUAL M S)
;;                (EQUAL C (ACL2::MOD-EXPT-FAST Z Q P))
;;                (EQUAL TT (ACL2::MOD-EXPT-FAST N Q P))
;;                (EQUAL R
;;                       (ACL2::MOD-EXPT-FAST N (* (+ Q 1) 1/2)
;;                                            P))
;;                (EQUAL (MOD (* R R) P)
;;                       (MOD (* TT N) P)))
;;           (EQUAL (MOD (* (T-S-AUX M C TT R P)
;;                          (T-S-AUX M C TT R P))
;;                       P)
;;                  (MOD N P))))

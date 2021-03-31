

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

;;copied from quadratic-residue.lisp
(defthm mod-expt-fast-instance-meaning
  (implies (and (rtl::primep p)
                (fep m p))
           (equal (acl2::mod-expt-fast m (/ (- p 1) 2) p)
                  (mod (expt m (/ (1- p) 2)) p)))
  :hints (("Goal" :in-theory (enable acl2::mod-expt-fast))))

(encapsulate
  ()
  (local
   (defthm T-S-aux-euler-criterion-lemma1
     (implies (and (rtl::primep p)
                   (< 2 p))
              (oddp p))
     :hints (("Goal"
              :in-theory (e/d (rtl::primep) (oddp))
              ))
     )
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
  )

(skip-proofs
 (defthm t-s-aux-equiv-lemma1-2
   (implies (and (natp z)
                 (rtl::primep p)
                 (natp p)
                 (< 2 p)
                 (= z 0))
            (has-square-root? z p))
   :hints (("Goal"
            :cases ((= z 0))
            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) ())
            :do-not-induct t
            ))
   )
 )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm t-s-aux-lemma-1
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c))
              (equal (expt (expt a b) c)
                     (expt a (* b c))))
     )
   )

  (local
   (defthm t-s-aux-lemma-2-1
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c))
              (equal (expt a (* b (expt 2 (- c 1))))
                     (expt a (/ (* b (expt 2 c)) 2)))))
   )

  (defthm T-S-aux-z-is-non-residue
    (implies (and (rtl::primep p)
                  (< 2 p)
                  (natp z)
                  (not (has-square-root? z p))
                  (< z p))
             (EQUAL (MOD (EXPT (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
                               (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P))))))
                         P)
                    (+ -1 P)))
    :hints (("Goal"
             
             :use ((:instance q2s-is-correct (n (- p 1)))
                   (:instance T-S-aux-euler-criterion (n z) (p p))
                   (:instance posp-Q*2^S-n-is-even (n (- p 1)))
                   (:instance Q*2^S-type-1 (n (- p 1)))
                   (:instance mv-nth-1!=0 (p p))
                   (:instance t-s-aux-lemma-1
                              (a z)
                              (b (MV-NTH 0 (Q*2^S (+ -1 P))))
                              (c (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                   )
             :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
             ))
    )

  (defthm T-S-aux-n-is-residue
    (implies (and (rtl::primep p)
                  (< 2 p)
                  (natp n)
                  (has-square-root? n p)
                  (> n 0)
                  (< n p))
             (EQUAL (MOD (EXPT (EXPT n (MV-NTH 0 (Q*2^S (+ -1 P))))
                               (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P))))))
                         P)
                    1))
    :hints (("Goal"
             
             :use ((:instance q2s-is-correct (n (- p 1)))
                   (:instance posp-Q*2^S-n-is-even (n (- p 1)))
                   (:instance Q*2^S-type-1 (n (- p 1)))
                   (:instance mv-nth-1!=0 (p p))
                   (:instance t-s-aux-lemma-1
                              (a z)
                              (b (MV-NTH 0 (Q*2^S (+ -1 P))))
                              (c (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                   )
             :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
             ))
    )
  )

(local
 (encapsulate
   ()

   (local
    (encapsulate
      ()

      (local (include-book "arithmetic-3/top" :dir :system))

      (defthm t-s-aux-equiv-subgoal1-2-2
        (implies (and (integerp a)
                      (integerp tt)
                      (natp a)
                      (integerp c))
                 (equal (* tt (expt c (expt 2 a)) (expt c (expt 2 a)))
                        (* tt (expt c (expt 2 (+ a 1)))))))
      )
    )
   
   (local
    (defthmd t-s-aux-equiv-subgoal1-2-3
      (implies (and (integerp m)
                    (integerp tt)
                    (rtl::primep p)
                    )
               (INTEGERP (+ -1
                            M (- (LEAST-REPEATED-SQUARE TT M P))))))
    )

   (local
    (defthm t-s-aux-equiv-subgoal-Goal
      (implies (and (integerp m)
                    (< 0 M)
                    )
               (NATP (+ -1
                        M (- (LEAST-REPEATED-SQUARE TT M P)))))
      :hints (("Goal"
               :use (:instance least-repeated-square-less-than-M (m m))
               ))
      )
    )

   (local
    (defthm t-s-aux-equiv-subgoal1-2
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
            (INTEGERP M)
            (< 0 M)
            (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
                   (+ -1 P))
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
        (MOD
         (EXPT
          (mod 
           (* TT
              (EXPT C
                    (EXPT 2
                          (+ -1
                             M (- (LEAST-REPEATED-SQUARE TT M P)))))
              (EXPT C
                    (EXPT 2
                          (+ -1
                             M (- (LEAST-REPEATED-SQUARE TT M P))))))
           p)
          (EXPT
           2
           (LEAST-REPEATED-SQUARE
            (MOD (* TT
                    (EXPT C
                          (EXPT 2
                                (+ -1
                                   M (- (LEAST-REPEATED-SQUARE TT M P)))))
                    (EXPT C
                          (EXPT 2
                                (+ -1
                                   M (- (LEAST-REPEATED-SQUARE TT M P))))))
                 P)
            (LEAST-REPEATED-SQUARE TT M P)
            P)))
         P)

        (MOD
         (EXPT
          (mod 
           (* TT
              (EXPT C
                    (EXPT 2
                          (+ M (- (LEAST-REPEATED-SQUARE TT M P)))))) p)
          (EXPT
           2
           (LEAST-REPEATED-SQUARE
            (MOD (* TT
                    (EXPT C
                          (EXPT 2
                                (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))
                 P)
            (LEAST-REPEATED-SQUARE TT M P)
            P)))
         P)
        )
       )

      :hints (("Goal"
               :use ((:instance t-s-aux-equiv-subgoal1-2-2
                                (c c)
                                (a (+ -1
                                      M (- (LEAST-REPEATED-SQUARE TT M P)))))
                     (:instance t-s-aux-equiv-subgoal1-2-3 (m m) (tt tt) (p p))
                     (:instance least-repeated-square-aux-less-than-M (m m))
                     )
               ))
      )
    )

   (local
    (encapsulate
      ()

      (local
       (encapsulate
         ()
         (local (include-book "rtl/rel11/lib/basic" :dir :system ))

         (local (include-book "arithmetic/equalities" :dir :system))

         (defthm t-s-aux-equiv-subgoal1-1-1-1-1
           (implies (and (integerp a)
                         (integerp b)
                         (integerp c)
                         (not (= c 0)))
                    (= (mod (* a b) c)
                       (mod (* (mod a c) (mod b c)) c))))

         (defthm t-s-aux-equiv-subgoal1-1-1-1-2
           (implies (and (integerp a)
                         (integerp b)
                         (integerp c)
                         (not (= c 0)))
                    (= (mod (* (mod a c) (mod b c)) c)
                       (mod (* a b) c)))
           :hints (("Goal"
                    :use (:instance t-s-aux-equiv-subgoal1-1-1-1-1
                                    (a a) (b b) (c c))
                    :in-theory nil
                    ))
           )

         (defthmd distributivity-of-expt-over-*
           (equal (expt (* a b) i)
                  (* (expt a i) (expt b i))))

         (defthmd exponents-add-unrestricted-equiv
           (implies (and (not (equal 0 r))
                         (acl2-numberp r)
                         (integerp i)
                         (integerp j))
                    (equal (* (expt r i) (expt r j))
                           (expt r (+ i j)))))

         (defthmd t-s-aux-equiv-subgoal1-1-1-1-3-sub2
           (implies (and (posp m)
                         (posp m1)
                         (< m1 m))
                    (INTEGERP (* (EXPT 2 M) (EXPT 2 (- M1)))))
           :hints (("Goal"
                    :use (:instance exponents-add-unrestricted-equiv
                                    (r 2)
                                    (i m)
                                    (j (- m1)))
                    :in-theory (disable acl2::expt-minus ACL2::EXPT-OF-UNARY-- ACL2::EXPONENTS-ADD)
                    ))
           )

         (defthmd t-s-aux-equiv-subgoal1-1-1-1-3
           (implies (and (posp m)
                         (posp m1)
                         (< m1 m)
                         (natp c))
                    (equal (EXPT (EXPT C (EXPT 2 (+ M (- M1))))
                                 (EXPT 2 (+ -1 M1)))
                           (expt c (expt 2 (- m 1)))))
           :hints (("Goal"
                    :use ((:instance acl2::exponents-multiply
                                     (i (EXPT 2 (+ M (- M1))))
                                     (j (EXPT 2 (+ -1 M1)))
                                     (r c))
                          (:instance exponents-add-unrestricted-equiv
                                     (r 2)
                                     (i m)
                                     (j (- m1)))
                          (:instance exponents-add-unrestricted-equiv
                                     (r 2)
                                     (i (+ -1 M1))
                                     (j (+ M (- M1)))
                                     )
                          )
                    :in-theory (disable acl2::expt-minus ACL2::EXPT-OF-UNARY--
                                        ACL2::EXPONENTS-ADD)
                    ))
           )

         (defthmd t-s-aux-equiv-subgoal1-1-1-1-4
           (implies (and (natp tt)
                         (posp m1))
                    (INTEGERP (EXPT TT (EXPT 2 (+ -1 M1)))))
           
           )
         )
       )
      
      (defthm t-s-aux-equiv-subgoal1-1-1-1
        (implies (and (posp p)
                      (< 2 p)
                      (posp m)
                      (posp m1)
                      (< m1 m)
                      (natp c)
                      (natp tt)
                      (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                      (= (mod (expt tt (expt 2 (- m1 1))) p) (mod -1 p)))
                 (equal (mod (expt (* tt (expt c (expt 2 (- m m1))))
                                   (expt 2 (- m1 1))) p)
                        1))
        :hints (("Goal"
                 :use ((:instance distributivity-of-expt-over-*
                                  (a tt)
                                  (b  (EXPT C
                                            (EXPT 2
                                                  (+ M (- m1)))))
                                  (i (EXPT
                                      2
                                      (- m1 1))))
                       (:instance t-s-aux-equiv-subgoal1-1-1-1-1
                                  (a (EXPT TT (EXPT 2 (+ -1 M1))))
                                  (b (EXPT C (EXPT 2 (+ -1 M))))
                                  (c p))
                       (:instance t-s-aux-equiv-subgoal1-1-1-1-2
                                  (a -1)
                                  (b -1)
                                  (c p))
                       (:instance t-s-aux-equiv-subgoal1-1-1-1-3
                                  (m m)
                                  (m1 m1)
                                  (c c)
                                  )
                       (:instance t-s-aux-equiv-subgoal1-1-1-1-4
                                  (tt tt)
                                  (m1 m1))
                       )
                 ))
        )
      )
    )
   
   (local
    (defthm t-s-aux-equiv-subgoal1-1-1
      (implies (and (rtl::primep p)
                    (< 2 p)
                    (posp m)
                    (posp (LEAST-REPEATED-SQUARE TT M P))
                    (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                    (EQUAL (MOD (EXPT TT
                                      (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
                                P)
                           1)
                    (natp c)
                    (natp tt))
               (EQUAL
                (MOD (EXPT (* TT
                              (EXPT C
                                    (EXPT 2
                                          (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))
                           (EXPT 2
                                 (+ -1 (LEAST-REPEATED-SQUARE TT M P))))
                     P)
                1))
      :hints (("Goal"
               :use ((:instance t-s-aux-equiv-subgoal1-1-1-1
                                (p p)
                                (m m)
                                (c c)
                                (m1 (least-repeated-square tt m p))
                                (tt tt))
                     (:instance y^2=1modp (p p)
                                (y
                                 (expt tt (expt 2 (- (least-repeated-square tt m p)
                                                     1)))))
                     (:instance t-s-aux-equiv-subgoal1-2-2
                                (tt 1)
                                (c tt)
                                (a (+ -1 (LEAST-REPEATED-SQUARE TT M P))))
                     (:instance least-repeated-square-is-least
                                (tt tt)
                                (m m)
                                (p p)
                                (d (least-repeated-square tt m p))
                                (i (- (least-repeated-square tt m p) 1)))
                     )
               :in-theory (e/d (acl2::mod-expt-fast) (least-repeated-square))
               ))

      )
    )
   
   (defthm t-s-aux-equiv-subgoal1-1
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
           (INTEGERP M)
           (< 0 M)
           (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
                  (+ -1 P))
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
       (MOD
        (EXPT
         (mod
          (* TT
             (EXPT C
                   (EXPT 2
                         (+ -1
                            M (- (LEAST-REPEATED-SQUARE TT M P)))))
             (EXPT C
                   (EXPT 2
                         (+ -1
                            M (- (LEAST-REPEATED-SQUARE TT M P))))))
          p)
         (EXPT
          2
          (LEAST-REPEATED-SQUARE
           (MOD (* TT
                   (EXPT C
                         (EXPT 2
                               (+ -1
                                  M (- (LEAST-REPEATED-SQUARE TT M P)))))
                   (EXPT C
                         (EXPT 2
                               (+ -1
                                  M (- (LEAST-REPEATED-SQUARE TT M P))))))
                P)
           (LEAST-REPEATED-SQUARE TT M P)
           P)))
        P)
       1))
     :hints (("Goal"
              :use (
                    (:instance least-repeated-square-not=0
                               (tt (mod (* TT
                                           (EXPT C
                                                 (EXPT 2
                                                       (+ M (- (LEAST-REPEATED-SQUARE
                                                                TT M P)))))) p))
                               (m (LEAST-REPEATED-SQUARE TT M P))
                               (i (- (LEAST-REPEATED-SQUARE TT M P) 1))
                               (p p))
                    )
              :in-theory (e/d () (least-repeated-square))
              ))
     )
   )
 )

;; (local
;;  (defthm t-s-aux-equiv-subgoal
;;    (implies (and (natp n)
;;                  (natp p)
;;                  (natp z)
;;                  (not (has-square-root? z p))
;;                  (< 2 p)
;;                  (< z p)
;;                  (rtl::primep p)
;;                  (< n p)
;;                  (has-square-root? n p)
;;                  (< 0 n)

;;                  (posp M);; x = S
;;                  (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p)) ;; c = (acl2::mod-expt-fast z Q p)
;; ;variables don't change                

;;                  (posp M) ; M =S
;;                  (natp c) ; (acl2::mod-expt-fast z Q p)
;;                  (natp tt) ; (acl2::mod-expt-fast n Q p)
;;                  (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

;;                  (equal (mod (* R R) p) (mod (* tt n) p))
;;                  (equal (least-repeated-square tt M p) M2)
;;                  (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))

;;             (if (zp M2)
;;                 (and (equal (mod (* R R) p) (mod n p))
;;                      (equal (T-S-aux M c tt R p) R)
;;                      )

;;               (let ((b (expt c (expt 2 (- (- M M2) 1)))))
;;                 (let (
;;                       (c2 (mod (* b b) p))
;;                       (tt2 (mod (* tt b b) p))
;;                       (R2 (mod (* R b) p)))
;;                   (declare (ignore R2 c2))
;;                   (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square
;;                                                        tt2 M2 p)) p) 1)
;;                   ))))
;;    :hints (("Goal"
;;             :use (:instance t-s-aux-equiv-subgoal1-1)
;;             :in-theory (e/d (acl2::mod-expt-fast) (least-repeated-square))
;;             :do-not-induct t
;;             ))
;;    )
;;  )



(local
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

   (local
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

                   (posp M);; M = S
                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p)) ;; c = (acl2::mod-expt-fast z Q p)
;variables don't change                

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

                         (posp M)
                         (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))             

                         (posp M2)
                         (natp c2)
                         (natp tt2)
                         (natp R2)

                         (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
                         
                         (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)

                         (< M2 M)

                         (equal (T-S-aux M c tt R p)
                                (T-S-aux M2 c2 tt2 R2 p))
                         )))))

     :hints (("Goal"
              :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square))
              :do-not-induct t
              )
             )
     )
   )
 )

---- 

(encapsulate
  ()

  (encapsulate
    ()

    (local (include-book "arithmetic-3/top" :dir :system))
    (local (include-book "arithmetic/top" :dir :system))

    (skip-proofs
     (defthm t-s-aux-equiv-subgoal1-3
       (implies (posp M)
                (integerp (EXPT 2
                                (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))))

    (defthm t-s-aux-equiv-subgoal1-4
      (implies (and (natp c)
                    (posp M))
               (equal (EXPT C
                            (* (EXPT 2 M)
                               (/ (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
                               (EXPT 2
                                     (+ -1 (LEAST-REPEATED-SQUARE TT M P)))))
                      (expt c (expt 2 (- M 1))))))
    
    )

  (local (include-book "arithmetic/equalities" :dir :system))
;(local (include-book "arithmetic-5/top" :dir :system))

  (defthm t-s-aux-equiv-subgoal1-1
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
          (INTEGERP M)
          (< 0 M)
          (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
                 (+ -1 P))
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
      (MOD
       (EXPT
        (mod
         (* TT
            (EXPT C
                  (EXPT 2
                        (+ -1
                           M (- (LEAST-REPEATED-SQUARE TT M P)))))
            (EXPT C
                  (EXPT 2
                        (+ -1
                           M (- (LEAST-REPEATED-SQUARE TT M P))))))
         p)
        (EXPT
         2
         (LEAST-REPEATED-SQUARE
          (MOD (* TT
                  (EXPT C
                        (EXPT 2
                              (+ -1
                                 M (- (LEAST-REPEATED-SQUARE TT M P)))))
                  (EXPT C
                        (EXPT 2
                              (+ -1
                                 M (- (LEAST-REPEATED-SQUARE TT M P))))))
               P)
          (LEAST-REPEATED-SQUARE TT M P)
          P)))
       P)
      1))
    :hints (("Goal"
             :use (
                   (:instance least-repeated-square-not=0
                              (tt (mod (* TT
                                          (EXPT C
                                                (EXPT 2
                                                      (+ M (- (LEAST-REPEATED-SQUARE
                                                               TT M P)))))) p))
                              (m (LEAST-REPEATED-SQUARE TT M P))
                              (i (- (LEAST-REPEATED-SQUARE TT M P) 1))
                              (p p))

                   (:instance least-repeated-square-not=0
                              (tt tt)
                              (m m)
                              (p p)
                              (i (least-repeated-square tt m p)))


                   (:instance acl2::exponents-multiply
                              (r c)
                              (i (expt 2 (- M (least-repeated-square tt m p))))
                              (j (expt 2 (+ -1 (LEAST-REPEATED-SQUARE TT M P)))))

                   (:instance t-s-aux-equiv-subgoal1-2-2
                              (tt 1)
                              (c tt)
                              (a (+ -1 (LEAST-REPEATED-SQUARE TT M P))))
                   
                   (:instance acl2::distributivity-of-expt-over-*
                              (a tt)
                              (b  (EXPT C
                                        (EXPT 2
                                              (+ M (- (LEAST-REPEATED-SQUARE TT
                                                                             M P))))))
                              (i (EXPT
                                  2
                                  (- (LEAST-REPEATED-SQUARE TT M P) 1))))
                   
                   (:instance least-repeated-square-is-least (tt tt)
                              (p p)
                              (i (LEAST-REPEATED-SQUARE
                                  (mod (* TT
                                          (EXPT C
                                                (EXPT 2
                                                      (+ M (- (LEAST-REPEATED-SQUARE
                                                               TT M P)))))) p)
                                  (LEAST-REPEATED-SQUARE TT M P)
                                  P)))

                   (:instance rtl::mod-mod-times
                              (n p)
                              (a (expt tt (EXPT
                                           2
                                           (- (LEAST-REPEATED-SQUARE TT M P)
                                              1))))
                              (b (expt c (expt 2 (- M 1)))))

                   (:instance rtl::mod-mod-times
                              (n p)
                              (b (mod (expt tt (EXPT
                                                2
                                                (- (LEAST-REPEATED-SQUARE TT M P)
                                                   1))) p))
                              (a (expt c (expt 2 (- M 1)))))

                   (:instance least-repeated-square-is-least
                              (tt tt)
                              (m m)
                              (p p)
                              (d (least-repeated-square tt m p))
                              (i (- (least-repeated-square tt m p) 1)))
                   
                   (:instance y^2=1modp (p p)
                              (y
                               (expt tt (expt 2 (- (least-repeated-square tt m p)
                                                   1)))))

                   ;; (:instance rtl::mod-mod-times
                   ;;            (n p)
                   ;;            (a -1)
                   ;;            (b (mod -1 p)))

                   ;; (:instance rtl::mod-mod-times
                   ;;            (n p)
                   ;;            (a -1)
                   ;;            (b -1))
                   
                   
                   )
             :in-theory (e/d (acl2::mod-expt-fast) (least-repeated-square))

             )
            ("Subgoal 4"
             :use ((:instance acl2::exponents-add-for-nonneg-exponents
                              (r 2)
                              (i M)
                              (j (- (least-repeated-square tt m p))))
                   (:instance t-s-aux-equiv-subgoal1-3 (m m)))
             
             )
            ("Subgoal 3"
             :use (:instance t-s-aux-equiv-subgoal1-3 (m m))
             )

            ("Subgoal 2"

             :use ((:instance rtl::mod-mod-times
                              (n p)
                              (a (expt tt (EXPT
                                           2
                                           (- (LEAST-REPEATED-SQUARE TT M P)
                                              1))))
                              (b (expt c (expt 2 (- M 1)))))

                   (:instance rtl::mod-mod-times
                              (n p)
                              (b (mod (expt tt (EXPT
                                                2
                                                (- (LEAST-REPEATED-SQUARE TT M P)
                                                   1))) p))
                              (a (expt c (expt 2 (- M 1)))))
                   
                   (:instance rtl::mod-mod-times
                              (n p)
                              (a -1)
                              (b (mod -1 p)))

                   (:instance rtl::mod-mod-times
                              (n p)
                              (a -1)
                              (b -1))

                   (:instance rtl::mod-mod-times
                              (n p)
                              (a (+ -1 p))
                              (b (EXPT C (EXPT 2 (+ -1 M)))))

                   (:instance rtl::mod-mod-times
                              (n p)
                              (b -1)
                              (a (EXPT C (EXPT 2 (+ -1 M)))))
                   
                   ))

            )
    )
  )
)

(local
 (defthm mod-expt-fast-instance-=
   (implies (and (natp p)
                 (integerp a)
                 (integerp c)
                 (fep a p))
            (equal (acl2::mod-expt-fast a c p)
                   (mod (expt a c) p)))
   :hints (("Goal" :in-theory (enable acl2::mod-expt-fast)))
   )
 )

(defthm t-s-aux-equiv-subgoal1
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

                (posp M);; x = S
                (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p)) ;; c = (acl2::mod-expt-fast z Q p)
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
                 (declare (ignore R2 c2))
                 (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square
                                                      tt2 M2 p)) p) 1)
                 ))))
  :hints (("Goal"

           :use (:instance mod-expt-fast-instance-= (p p)
                           (a (mod (* tt b b) p))
                           (c (expt 2 (least-repeated-square tt2 M2 p))))
           :in-theory (e/d (acl2::mod-expt-fast) (least-repeated-square))
           :do-not-induct t
           ))
  )

;-----

;; (local
;;  (defthm t-s-aux-equiv-subgoal1-1-1
;;    (implies (and (rationalp a)
;;                  (rationalp b)
;;                  (natp a)
;;                  (natp b))
;;             (equal (* (expt c a) (expt c b))
;;                    (expt c (+ a b))))))

;; (local
;;  (defthm t-s-aux-equiv-subgoal1-1
;;    (implies (and (integerp a)
;;                  (natp a)
;;                  (integerp c))
;;             (equal (* (expt c (expt 2 a)) (expt c (expt 2 a)))
;;                    (expt c (expt 2 (+ a 1)))))))

;; (local
;;  (skip-proofs
;;   (defthm t-s-aux-equiv-subgoal1-2
;;     (IMPLIES
;;      (AND (INTEGERP N)
;;           (<= 0 N)
;;           (<= 0 P)
;;           (INTEGERP Z)
;;           (<= 0 Z)
;;           (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                       1))
;;           (< 2 P)
;;           (< Z P)
;;           (RTL::PRIMEP P)
;;           (< N P)
;;           (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;                  1)
;;           (< 0 N)
;;           (INTEGERP M)
;;           (< 0 M)
;;           (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
;;                  (+ -1 P))
;;           (INTEGERP C)
;;           (<= 0 C)
;;           (INTEGERP TT)
;;           (<= 0 TT)
;;           (INTEGERP R)
;;           (<= 0 R)
;;           (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
;;           (EQUAL (MOD (EXPT TT
;;                             (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
;;                       P)
;;                  1)
;;           (< 0 (LEAST-REPEATED-SQUARE TT M P)))
;;      (EQUAL
;;       (MOD
;;        (EXPT
;;         (* TT
;;            (EXPT C
;;                  (EXPT 2
;;                        (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;         (EXPT
;;          2
;;          (- (LEAST-REPEATED-SQUARE TT M P) 1)))
;;        p)
;;       1))
;;     )
;;   )
;;  )

;; (local
;;  (skip-proofs
;;   (defthm t-s-aux-subgoal1-3
;;     (implies (and (INTEGERP N)
;;                   (<= 0 N)
;;                   (<= 0 P)
;;                   (INTEGERP Z)
;;                   (<= 0 Z)
;;                   (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                               1))
;;                   (< 2 P)
;;                   (< Z P)
;;                   (RTL::PRIMEP P)
;;                   (< N P)
;;                   (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;                          1)
;;                   (< 0 N)
;;                   (INTEGERP M)
;;                   (< 0 M)
;;                   (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
;;                          (+ -1 P))
;;                   (INTEGERP C)
;;                   (<= 0 C)
;;                   (INTEGERP TT)
;;                   (<= 0 TT)
;;                   (INTEGERP R)
;;                   (<= 0 R)
;;                   (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
;;                   (EQUAL (MOD (EXPT TT
;;                                     (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
;;                               P)
;;                          1)
;;                   (< 0 (LEAST-REPEATED-SQUARE TT M P)))
;;              (AND (INTEGERP (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P))))
;;                   (NATP (+ -1 (LEAST-REPEATED-SQUARE TT M P)))
;;                   (NATP (* TT
;;                            (EXPT C
;;                                  (EXPT 2
;;                                        (+ M
;;                                           (- (LEAST-REPEATED-SQUARE TT M P))))))))))
;;   )
;;  )

;; (local
;;  (defthm t-s-aux-equiv-subgoal1-8
;;    (IMPLIES
;;     (AND
;;      (EQUAL (* (EXPT C
;;                      (EXPT 2
;;                            (+ -1
;;                               M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;                (EXPT C
;;                      (EXPT 2
;;                            (+ -1
;;                               M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;             (EXPT C
;;                   (EXPT 2
;;                         (+ (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                            1))))
;;      (=
;;       (MOD
;;        (EXPT
;;         (* TT
;;            (EXPT C
;;                  (EXPT 2
;;                        (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;         (EXPT 2
;;               (LEAST-REPEATED-SQUARE
;;                (* TT
;;                   (EXPT C
;;                         (EXPT 2
;;                               (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;                (LEAST-REPEATED-SQUARE TT M P)
;;                P)))
;;        P)
;;       1)
;;      (INTEGERP (+ -1
;;                   M (- (LEAST-REPEATED-SQUARE TT M P))))
;;      (NATP (+ -1 (LEAST-REPEATED-SQUARE TT M P)))
;;      (NATP (* TT
;;               (EXPT C
;;                     (EXPT 2
;;                           (+ M
;;                              (- (LEAST-REPEATED-SQUARE TT M P)))))))
;;      (INTEGERP N)
;;      (<= 0 N)
;;      (<= 0 P)
;;      (INTEGERP Z)
;;      (<= 0 Z)
;;      (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                  1))
;;      (< 2 P)
;;      (< Z P)
;;      (RTL::PRIMEP P)
;;      (< N P)
;;      (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;             1)
;;      (< 0 N)
;;      (INTEGERP M)
;;      (< 0 M)
;;      (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
;;             (+ -1 P))
;;      (INTEGERP C)
;;      (<= 0 C)
;;      (INTEGERP TT)
;;      (<= 0 TT)
;;      (INTEGERP R)
;;      (<= 0 R)
;;      (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
;;      (EQUAL (MOD (EXPT TT
;;                        (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
;;                  P)
;;             1)
;;      (< 0 (LEAST-REPEATED-SQUARE TT M P)))
;;     (EQUAL
;;      (MOD
;;       (EXPT
;;        (* TT
;;           (EXPT C
;;                 (EXPT 2
;;                       (+ (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                          1))))
;;        (EXPT
;;         2
;;         (LEAST-REPEATED-SQUARE
;;          (MOD (* TT
;;                  (EXPT C
;;                        (EXPT 2
;;                              (+ (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))
;;                                 1))))
;;               P)
;;          (LEAST-REPEATED-SQUARE TT M P)
;;          P)))
;;       P)
;;      1))
;;    :hints (("Goal"
;;             :in-theory (e/d () (least-repeated-square mod expt))
;;             ))
;;            )
;;    )


;; (defthm t-s-aux-equiv-subgoal1
;;   (IMPLIES
;;    (AND (INTEGERP N)
;;         (<= 0 N)
;;         (<= 0 P)
;;         (INTEGERP Z)
;;         (<= 0 Z)
;;         (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                     1))
;;         (< 2 P)
;;         (< Z P)
;;         (RTL::PRIMEP P)
;;         (< N P)
;;         (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;                1)
;;         (< 0 N)
;;         (INTEGERP M)
;;         (< 0 M)
;;         (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
;;                (+ -1 P))
;;         (INTEGERP C)
;;         (<= 0 C)
;;         (INTEGERP TT)
;;         (<= 0 TT)
;;         (INTEGERP R)
;;         (<= 0 R)
;;         (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
;;         (EQUAL (MOD (EXPT TT
;;                           (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
;;                     P)
;;                1)
;;         (< 0 (LEAST-REPEATED-SQUARE TT M P)))
;;    (EQUAL
;;     (MOD
;;      (EXPT
;;       (* TT
;;          (EXPT C
;;                (EXPT 2
;;                      (+ -1
;;                         M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;          (EXPT C
;;                (EXPT 2
;;                      (+ -1
;;                         M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;       (EXPT
;;        2
;;        (LEAST-REPEATED-SQUARE
;;         (MOD (* TT
;;                 (EXPT C
;;                       (EXPT 2
;;                             (+ -1
;;                                M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;                 (EXPT C
;;                       (EXPT 2
;;                             (+ -1
;;                                M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;              P)
;;         (LEAST-REPEATED-SQUARE TT M P)
;;         P)))
;;      P)
;;     1))

;;   :hints (("Goal"
;;            ;; :use ((:instance t-s-aux-equiv-subgoal1-1
;;            ;;                 (c c)
;;            ;;                 (a (+ -1
;;            ;;                       M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;            ;;       (:instance least-repeated-square-not=0
;;            ;;                  (tt (* TT
;;            ;;                         (EXPT C
;;            ;;                               (EXPT 2
;;            ;;                                     (+ M (- (LEAST-REPEATED-SQUARE
;;            ;;                                              TT M P)))))))
;;            ;;                  (m (LEAST-REPEATED-SQUARE TT M P))
;;            ;;                  (i (- (LEAST-REPEATED-SQUARE TT M P) 1))
;;            ;;                  (p p))
;;            ;;       (:instance t-s-aux-subgoal1-3)
;; ;)
;; ;:in-theory nil

;;            ))



;;   )

;; (encapsulate
;;   ()

;;   (local
;;    (defthmd t-s-aux-equiv-lemma1-1
;;      (implies (and (integerp a)
;;                    (integerp p)
;;                    (> p 0))
;;               (equal (mod (* a (mod a p)) p)
;;                      (mod (* a a) p))))
;;    )

;;   (defthm t-s-aux-equiv-lemma1
;;     (IMPLIES
;;      (AND (INTEGERP N)
;;           (<= 0 N)
;;           (<= 0 P)
;;           (INTEGERP Z)
;;           (<= 0 Z)
;;           (NOT (EQUAL (MOD (EXPT Z (+ -1/2 (* 1/2 P))) P)
;;                       1))
;;           (< 2 P)
;;           (< Z P)
;;           (RTL::PRIMEP P)
;;           (< N P)
;;           (EQUAL (MOD (EXPT N (+ -1/2 (* 1/2 P))) P)
;;                  1)
;;           (< 0 N)
;;           (INTEGERP X)
;;           (<= 0 X)
;;           (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 X))) P)
;;                  (+ -1 P))
;;           (INTEGERP M)
;;           (< 0 M)
;;           (INTEGERP C)
;;           (<= 0 C)
;;           (INTEGERP TT)
;;           (<= 0 TT)
;;           (INTEGERP R)
;;           (<= 0 R)
;;           (EQUAL (MOD (* R R) P) (MOD (* N TT) P))
;;           (EQUAL (MOD (EXPT TT
;;                             (EXPT 2 (LEAST-REPEATED-SQUARE TT M P)))
;;                       P)
;;                  1)
;;           (< 0 (LEAST-REPEATED-SQUARE TT M P)))
;;      (EQUAL
;;       (MOD (* R
;;               (EXPT C
;;                     (EXPT 2
;;                           (+ -1
;;                              M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;               (MOD (* R
;;                       (EXPT C
;;                             (EXPT 2
;;                                   (+ -1
;;                                      M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;                    P))
;;            P)
;;       (MOD (* N TT
;;               (EXPT C
;;                     (EXPT 2
;;                           (+ -1
;;                              M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;               (EXPT C
;;                     (EXPT 2
;;                           (+ -1
;;                              M (- (LEAST-REPEATED-SQUARE TT M P))))))
;;            P)))
;;     :hints (("Goal"
;;              :use ((:instance t-s-aux-equiv-lemma1-1
;;                               (a (* R
;;                                     (EXPT C
;;                                           (EXPT 2
;;                                                 (+ -1
;;                                                    M (- (LEAST-REPEATED-SQUARE
;;                                                          TT M P)))))))
;;                               (p p))
;;                    (:instance rtl::mod-times-mod
;;                               (a (* R R))
;;                               (b (* N tt))
;;                               (c
;;                                (* (EXPT C
;;                                         (EXPT 2
;;                                               (+ -1
;;                                                  M (- (LEAST-REPEATED-SQUARE TT M P)))))
;;                                   (EXPT C
;;                                         (EXPT 2
;;                                               (+ -1
;;                                                  M (- (LEAST-REPEATED-SQUARE TT
;;                                                                              M P))))))
;;                                )
;;                               (n p))
;;                    )
;;              :in-theory (e/d () (least-repeated-square))
;;              ))
;;     )

;;   (defthm t-s-aux-equiv
;;     (implies (and (natp n)
;;                   (natp p)
;;                   (natp z)
;;                   (not (has-square-root? z p))
;;                   (< 2 p)
;;                   (< z p)
;;                   (rtl::primep p)
;;                   (< n p)
;;                   (has-square-root? n p)
;;                   (< 0 n)

;;                   (posp M);; M = S
;;                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p)) ;; c = (acl2::mod-expt-fast z Q p)
;; ;variables don't change                

;;                   (natp c) ; (acl2::mod-expt-fast z Q p)
;;                   (natp tt) ; (acl2::mod-expt-fast n Q p)
;;                   (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

;;                   (equal (mod (* R R) p) (mod (* tt n) p))
;;                   (equal (least-repeated-square tt M p) M2)
;;                   (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))

;;              (if (zp M2)
;;                  (and (equal (mod (* R R) p) (mod n p))
;;                       (equal (T-S-aux M c tt R p) R)
;;                       )

;;                (let ((b (expt c (expt 2 (- (- M M2) 1)))))
;;                  (let (
;;                        (c2 (mod (* b b) p))
;;                        (tt2 (mod (* tt b b) p))
;;                        (R2 (mod (* R b) p)))
;;                    (and (natp n)
;;                         (natp p)
;;                         (natp z)
;;                         (not (has-square-root? z p))
;;                         (< 2 p)
;;                         (< z p)
;;                         (rtl::primep p)
;;                         (< n p)
;;                         (has-square-root? n p)
;;                         (< 0 n)

;;                         (posp M);; x = S
;;                         (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p)) ;; c = z^Q
;; ;variables don't change                

;;                         (posp M2)
;;                         (natp c2) ; (acl2::mod-expt-fast z Q p)
;;                         (natp tt2) ; (acl2::mod-expt-fast n Q p)
;;                         (natp R2) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

;;                         (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
;; ;(equal (least-repeated-square tt2 M2 p) M3)
;;                         (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)

;;                         (< M2 M)

;; ;(equal (T-S-aux M c tt R p)
;; ;      (T-S-aux M2 c2 tt2 R2 p))
;;                         )))))

;;     :hints (("Goal"
;; ;:use (:instance least-repeated-square-equiv-2 (tt tt) (m e) (p p))
;;              :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square))
;;              :do-not-induct t
;;              )
;;             ("Subgoal 1"
;;              :use (:instance t-s-aux-equiv-subgoal1
;;                              (M2 (least-repeated-square tt M p)))
;;              )

;;             )
;;     )
;;   )


;; (encapsulate
;;   ()
;;   (local (include-book "arithmetic-5/top" :dir :system))

;;   (defthm hyps-true-T-S-aux-1
;;     (implies (and (rtl::primep p)
;;                   (< 2 p)
;;                   (< 0 n)
;;                   (< n p)
;;                   (natp n))
;;              (EQUAL (MOD (* (EXPT N
;;                                   (+ 1/2
;;                                      (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P))))))
;;                             (EXPT N
;;                                   (+ 1/2
;;                                      (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))))
;;                          P)
;;                     (MOD (* N (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P)))))
;;                          P)))
;;     :hints (("Goal"
;;              :in-theory (e/d (acl2::not-evenp-when-oddp) ())
;;              ))
;;     )
;;   )

;; (defthm hyps-true-T-S-aux
;;   (implies (and (natp n)
;;                 (natp p)
;;                 (natp z)
;;                 (not (has-square-root? z p))
;;                 (< 2 p)
;;                 (< z p)
;;                 (rtl::primep p)
;;                 (< n p)
;;                 (has-square-root? n p)
;;                 (< 0 n)

;; ;(equal (mv-nth 1 (Q*2^S (- p 1))) x)

;;                 (equal (mv-nth 1 (Q*2^S (- p 1))) M)
;;                 (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
;;                 (equal (acl2::mod-expt-fast z Q p) c)
;;                 (equal (acl2::mod-expt-fast n Q p) tt)
;;                 (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R)

;;                 (equal (least-repeated-square tt M p) M2))

;;            (and
;; ;(posp x)
;;             (posp M) ; M =S
;;             (natp c) ; (acl2::mod-expt-fast z Q p)
;;             (natp tt) ; (acl2::mod-expt-fast n Q p)
;;             (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

;;             (equal (mod (* R R) p) (mod (* tt n) p))

;;             (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))

;;             (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)))
;;   :hints (("Goal"
;;            :use ((:instance least-repeated-square-not=0
;;                             (m M)
;;                             (i (- M 1))
;;                             (p p))
;;                  (:instance q2s-is-correct (n (- p 1))))
;;            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) (least-repeated-square))
;;            :do-not-induct t
;;            ))
;;   )

;; (local
;;  (defthm t-s-aux-lemma-1
;;    (implies (and (integerp a)
;;                  (integerp p)
;;                  (> p 0))
;;             (equal (mod (* a (mod a p)) p)
;;                    (mod (* a a) p))))
;;  )

;; (local
;;  (defun inv-p (M c tt r p)




;;    (defthm t-s-aux-lemma
;;      (implies (and (natp n)
;;                    (< 0 n)
;;                    (natp p)
;;                    (natp z)
;; ;(> z 0)
;;                    (< 2 p)
;;                    (< z p)
;;                    (rtl::primep p)
;;                    (< n p)
;;                    (has-square-root? n p)
;;                    (not (has-square-root? z p)))
;;               (equal (mod (* (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                       (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                       (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                       (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                       p)
;;                              (T-S-aux (mv-nth 1 (Q*2^S (- p 1)))
;;                                       (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                       (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                       (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p)
;;                                       p)
;;                              )
;;                           p)
;;                      (mod n p)))
;;      :hints (("Goal"
;;               :use (
;;                     (:instance q2s-is-correct (n (- p 1)))
;;                     (:instance posp-Q*2^S-n-is-even (n (- p 1)))
;;                     (:instance t-s-aux-equiv
;;                                (n n)
;;                                (p p)
;;                                (z z)
;;                                (M (mv-nth 1 (Q*2^S (- p 1))))
;; ;(Q (mv-nth 0 (Q*2^S (- p 1))))
;;                                (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
;;                                (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
;;                                (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                                (M2 (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                                           (mv-nth 1 (Q*2^S (- p
;;                                                                               1))) p)))
;;                     (:instance hyps-true-T-S-aux
;;                                (n n)
;;                                (p p)
;;                                (z z)
;;                                (M (mv-nth 1 (Q*2^S (- p 1))))
;;                                (Q (mv-nth 0 (Q*2^S (- p 1))))
;;                                (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
;;                                (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
;;                                (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
;;                                (M2 (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p)
;;                                                           (mv-nth 1 (Q*2^S (- p
;;                                                                               1))) p)))
;;                     )
;;               :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) (least-repeated-square))
;;               )

;;              )
;;      )

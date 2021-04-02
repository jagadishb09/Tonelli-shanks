

(in-package "PRIMES")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(include-book "kestrel/number-theory/tonelli-shanks-test" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields" :dir :system))
(local (include-book "kestrel/crypto/ecurve/primes" :dir :system))
(local (include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system))
(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))

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
  (local (include-book "divides"))
  
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

   (local (include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system))

   (skip-proofs
    (defthm mod-theorem-three
      (implies (and (integerp a)
                    (integerp i)
                    (<= 0 i)
                    (integerp n)
                    (not (equal n 0))
                    (integerp x))
               (equal (mod (* x (expt (mod a n) i)) n)
                      (mod (* x (expt a i)) n)))
      )
    )
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

      
      (encapsulate
        ()
        (local (in-theory nil))

        (local (include-book "arithmetic-5/top" :dir :system))
        (local (include-book "kestrel/arithmetic-light/mod" :dir :system))
        (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
        (local (include-book "kestrel/arithmetic-light/times" :dir :system))
        (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
        (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
        (local (include-book "kestrel/number-theory/tonelli-shanks-test" :dir :system))
        
        (defthm t-s-aux-equiv-subgoal1-3-lemma
          (implies (and (natp n)
                        (natp p)
                        (< 2 p)
                        (rtl::primep p)
                        (< n p)
                        (has-square-root? n p)
                        (< 0 n)
                        (posp M)
                        (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))            

                        (natp c)
                        (natp tt)
                        (natp R)

                        (equal (mod (* R R) p) (mod (* tt n) p))
                        (equal (least-repeated-square tt M p) M2)
                        (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)
                        (> M2 0))

                   (let ((b (expt c (expt 2 (- (- M M2) 1)))))
                     (let (
                           (c2 (mod (* b b) p))
                           (tt2 (mod (* tt b b) p))
                           (R2 (mod (* R b) p)))
                       (declare (ignore R2 tt2))

                       (equal (mod (expt c2 (expt 2 (- M2 1))) p) (mod -1 p))
                       )))
          :hints (("Goal"
                   :use(
                        (:instance t-s-aux-equiv-subgoal1-2-2
                                   (tt 1)
                                   (c c)
                                   (a (- (-  M M2) 1)) 
                                   )
                        (:instance mod-theorem-three
                                   (x 1)
                                   (n p)
                                   (i (EXPT 2
                                            (+ -1 M2)))
                                   (a (EXPT C
                                            (EXPT 2 (+ M (- M2))))))
                        (:instance t-s-aux-equiv-subgoal1-1-1-1-3
                                   (m m)
                                   (m1 m2)
                                   (c c))
                        (:instance t-s-aux-equiv-subgoal1-2-3
                                   (tt tt)
                                   (m m)
                                   (p p))
                        (:instance least-repeated-square-less-than-M
                                   (m m)
                                   (tt tt)
                                   (p p))
                        )
                   
                   :in-theory 
                   (e/d (acl2::mod-expt-fast zp expt) (least-repeated-square has-square-root?
                                                                             MOD-THEOREM-THREE
                                                                             T-S-AUX-EQUIV-SUBGOAL1-2-3
                                                                             T-S-AUX-EQUIV-SUBGOAL1-1-1-1-3
                                                                             t-s-aux-equiv-subgoal1-2
                                                                             t-s-aux-equiv-subgoal-Goal
                                                                             t-s-aux-equiv-subgoal1-2-2
                                                                             T-S-aux-n-is-residue
                                                                             T-S-aux-z-is-non-residue
                                                                             t-s-aux-equiv-lemma1-2
                                                                             T-S-aux-euler-criterion
                                                                             least-repeated-square-is-least
                                                                             least-repeated-square-aux-not=0-10
                                                                             least-repeated-square-aux-not=0-9
                                                                             least-repeated-square-not=0
                                                                             y^2=1modp
                                                                             y^2=1modp-lemma1
                                                                             ))
                   ))
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
           (< 2 P)
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
                    (:instance mod-theorem-three (x 1)
                               (a (* TT
                                     (EXPT C
                                           (EXPT 2
                                                 (+ M (- (LEAST-REPEATED-SQUARE TT M P)))))))
                               (i (EXPT 2
                                        (+ -1 (LEAST-REPEATED-SQUARE TT M P))))
                               (n p))
                    (:instance least-repeated-square-not=0
                               (tt (mod (* TT
                                           (EXPT C
                                                 (EXPT 2
                                                       (+ M (- (LEAST-REPEATED-SQUARE
                                                                TT M P)))))) p))
                               (m (LEAST-REPEATED-SQUARE TT M P))
                               (i (- (LEAST-REPEATED-SQUARE TT M P) 1))
                               (p p))
                    (:instance t-s-aux-equiv-subgoal1-1-1 (tt tt) (m m) (p p))
                    )
              :in-theory (e/d () (least-repeated-square))
              ))
     )

   (defthm t-s-aux-equiv-subgoal1-3
     (implies (and (natp n)
                   (natp p)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (< 0 n)
                   (posp M)
                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))            
                   (natp c)
                   (natp tt)
                   (natp R)
                   (equal (mod (* R R) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt M p) M2)
                   (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)
                   (> M2 0))
              
              (let ((b (expt c (expt 2 (- (- M M2) 1)))))
                (let (
                      (c2 (mod (* b b) p))
                      (tt2 (mod (* tt b b) p))
                      (R2 (mod (* R b) p)))
                  (declare (ignore R2 tt2))

                  (equal (mod (expt c2 (expt 2 (- M2 1))) p) (mod -1 p))
                  )))
     :hints (("Goal"
              :use (
                    (:instance t-s-aux-equiv-subgoal1-3-lemma)
                    )
              ))
     )

   
   )
 )

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm hyps-true-T-S-aux-1
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
 )

(local
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

                 (equal (mv-nth 1 (Q*2^S (- p 1))) M)
                 (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
                 (equal (acl2::mod-expt-fast z Q p) c)
                 (equal (acl2::mod-expt-fast n Q p) tt)
                 (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R)

                 (equal (least-repeated-square tt M p) M2))

            (and
             (posp M) ; M =S
             (natp c) ; (acl2::mod-expt-fast z Q p)
             (natp tt) ; (acl2::mod-expt-fast n Q p)
             (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)

             (equal (mod (* R R) p) (mod (* tt n) p))

             (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))

             (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)))
   :hints (("Goal"
            :use ((:instance least-repeated-square-not=0
                             (m M)
                             (i (- M 1))
                             (p p))
                  (:instance mod-theorem-three (a (EXPT N (MV-NTH 0 (Q*2^S (+
                                                                            -1 P)))))
                             (n p)
                             (x 1)
                             (i (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                  (:instance mod-theorem-three (a (EXPT Z (MV-NTH 0 (Q*2^S (+
                                                                            -1 P)))))
                             (n p)
                             (x 1)
                             (i (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                  (:instance q2s-is-correct (n (- p 1))))
            :in-theory (e/d (ACL2::MOD-EXPT-FAST acl2::not-evenp-when-oddp) (least-repeated-square))
            :do-not-induct t
            ))
   )
 )


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
            (< 2 P)
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
;n M c tt R p
   (defthmd t-s-aux-equiv-lemma
     (implies (and (natp n)
                   (natp p)
                   (< 2 p)
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
                  (equal (mod (* R R) p) (mod n p))
                ;(equal (T-S-aux M c tt R p) R)
                 ;      )

                (let ((b (expt c (expt 2 (- (- M M2) 1)))))
                  (let (
                        (c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (R2 (mod (* R b) p)))
                    (and (natp n)
                         (natp p)
                         (< 2 p)
                         (rtl::primep p)
                         (< n p)
                         (has-square-root? n p)
                         (< 0 n)

                         ;(posp M)
                         ;(equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))             

                         (posp M2)
                         (natp c2)
                         (natp tt2)
                         (natp R2)

                         (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
                         
                         (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)

                         (< M2 M)

                         (equal (mod (expt c2 (expt 2 (- M2 1))) p) (mod -1 p))

                         ;(equal (T-S-aux M c tt R p)
                          ;      (T-S-aux M2 c2 tt2 R2 p))
                         )))))

     :hints (("Goal"
              :use (:instance t-s-aux-equiv-subgoal1-3)
              :in-theory (e/d (ACL2::MOD-EXPT-FAST) (least-repeated-square hyps-true-T-S-aux))
              :do-not-induct t
              )
             )
     )
   )
 )

(defthm t-s-aux-equiv-1
  (implies (and (natp n)
                (natp p)
                (< 2 p)
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
                (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)
                (> M2 0))

           ;; (if (zp M2)
           ;;     (equal (mod (* R R) p) (mod n p))

             (let ((b (expt c (expt 2 (- (- M M2) 1)))))
               (let (
                     (c2 (mod (* b b) p))
                     (tt2 (mod (* tt b b) p))
                     (R2 (mod (* R b) p)))
                 ;(declare (ignore c2 tt2 r2))
                 (and (natp n)
                      (natp p)
                      (< 2 p)
                      (rtl::primep p)
                      (< n p)
                      (has-square-root? n p)
                      (< 0 n)

                      ;(posp M)
                      ;(equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))             

                      (posp M2)
                      (natp c2)
                      (natp tt2)
                      (natp R2)

                      (equal (mod (* R2 R2) p) (mod (* tt2 n) p))
                      
                      (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)

                      (< M2 M)

                      (equal (mod (expt c2 (expt 2 (- M2 1))) p) (mod -1 p))
                      ))))

  :hints (("Goal"
           :use (:instance t-s-aux-equiv-lemma)
           :in-theory (e/d () (acl2::mod-expt-fast least-repeated-square hyps-true-T-S-aux))
           :do-not-induct t
           )
          )
  )

(defthm t-s-aux-equiv-2
  (implies (and (natp n)
                (natp p)
                (< 2 p)
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
               (equal (mod (* R R) p) (mod n p))
             t))
    :hints (("Goal"
           :use (:instance t-s-aux-equiv-lemma)
           :in-theory (e/d () (acl2::mod-expt-fast least-repeated-square hyps-true-T-S-aux))
           :do-not-induct t
           )
          )
  )

(encapsulate
  ()
  
  (local
   (defthm T-S-aux-subgoal
     (IMPLIES (NOT (ZP (LEAST-REPEATED-SQUARE TT M P)))
              (O< (NFIX (LEAST-REPEATED-SQUARE TT M P))
                  (NFIX M)))
     :hints (("Goal"
              :use (:instance least-repeated-square-aux-less-than-M (i 1) (tt tt)
                              (m m) (p p))
              ))
     )
   )

  (define T-S-aux-= (n M c tt R p)
    (declare (xargs :measure (nfix M)
                    :guard-debug t
                    :guard (and (posp M) (natp c) (natp tt) (natp R) (posp n)
                                (rtl::primep p) (< 2 p))
                    :hints (("Goal"
                             :use (:instance T-S-aux-subgoal
                                             (tt tt) (m m) (p p))
                             ))
                    ))
    (let ((M2 (least-repeated-square tt M p)))
      (if (zp M2)
          R
        (let ((b (expt c (expt 2 (- (- M M2) 1)))))
          (let (
                (c2 (mod (* b b) p))
                (tt2 (mod (* tt b b) p))
                (R2 (mod (* R b) p)))
            (T-S-aux-= n M2 c2 tt2 R2 p))))))

  (local
   (defthm T-s-aux-=T-s-aux
     (implies (posp n)
              (equal (T-S-aux-= n M c tt R p)
                     (T-S-aux M c tt R p)))
     :hints (("Goal"
              :in-theory (e/d (T-s-aux-=) (least-repeated-square))
              ))
     )
   )

  (defthm integerp-T-S-aux-=
    (implies  (and (posp n)
                   (natp M)
                   (natp c)
                   (natp tt)
                   (natp R)
                   (natp p)
                   (< 2 p))
              (natp (T-S-aux-= n M c tt R p)))
    )
  )



(encapsulate
  ()

  (local
   (defthm T-s-aux-=T-s-aux
     (implies (posp n)
              (equal (T-S-aux-= n M c tt R p)
                     (T-S-aux M c tt R p)))
     :hints (("Goal"
              :in-theory (e/d (T-s-aux-=) (least-repeated-square))
              ))
     )
   )

  (local (include-book "projects/quadratic-reciprocity/eisenstein" :dir :system))
  (define tonelli-shanks-has-sqrt-= ((n natp) (p natp) (z natp))
    :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (has-square-root? n p) (not (has-square-root? z p)))
    :guard-debug t
    :short "Tonelli-Shanks modular square root."
    :long "Finds the square root of n modulo p.  p must be an odd prime.
         z is a quadratic nonresidue in p."
    :returns (sqrt natp :hyp :guard :hints (("Goal"
                                             :in-theory (e/d (natp) (t-s-aux-equiv-1))
                                             )))

    (if (= n 0)
        0
      (mv-let (Q S)
        (Q*2^S (- p 1))
        (let (
              (M S)
              (c (acl2::mod-expt-fast z Q p))
              (tt (acl2::mod-expt-fast n Q p))
              (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
          (T-S-aux-= n M c tt R p))))
    :guard-hints (("Goal"
                   :in-theory (e/d (acl2::integerp-of-*-of-1/2-becomes-evenp
                                    acl2::not-evenp-when-oddp
                                    acl2::mod-expt-fast
                                    rtl::oddp-odd-prime
                                    natp)
                                   (oddp)))))
  
  )

--

(encapsulate
  ()

  (skip-proofs
   (local
    (defthmd sub*1/2.5
      (EQUAL (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
                  P)
             (MOD (* (EXPT (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
                                P)
                           1/2)
                     (EXPT (MOD (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P))))
                                P)
                           1/2))
                  P))))
   )
  
  (defthm tonelli-shanks-is-sqrt-modp
    (implies (and (natp n)
                  (natp p)
                  (natp z)
                  (> p 2)
                  (< z p)
                  (rtl::primep p)
                  (not (has-square-root? z p))
                  (> n 0)
                  (equal (mv-nth 1 (Q*2^S (- p 1))) M)
                  (equal (mv-nth 0 (Q*2^S (- p 1))) Q)
                  (equal (acl2::mod-expt-fast z Q p) c)
                  (equal (acl2::mod-expt-fast n Q p) tt)
                  (equal (acl2::mod-expt-fast n (/ (+ Q 1) 2) p) R))
;(equal (tonelli-shanks-has-sqrt-= n p z) y))
;(not (= y 0)))
             (= (mod (expt (T-S-AUX-= n M c tt R p) 2) p) n))
    :hints (("Goal"

;:use (:instance tonelli-shanks-has-sqrt-= (n n) (p p) (z z))
;:induct (rev1-modified x a (fact k)))))
; :use (
;(:instance t-s-aux-equiv-1
             ;;                  (n n)
             ;;                  (p p)
             ;;                  (M (mv-nth 1 (Q*2^S (- p 1))))
             ;;                  (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
             ;;                  (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
             ;;                  (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
             ;;                  (M2 (least-repeated-square (acl2::mod-expt-fast n
             ;;                                                                  (mv-nth 0 (Q*2^S (- p 1))) p)
             ;;                                             (mv-nth 1 (Q*2^S (- p 1))) p)))
             ;;       (:instance t-s-aux-equiv-2
             ;;                  (n n)
             ;;                  (p p)
             ;;                  (M (mv-nth 1 (Q*2^S (- p 1))))
             ;;                  ;(Q (mv-nth 0 (Q*2^S (- p 1))))
             ;;                  (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
             ;;                  (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
             ;;                  (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
             ;;                  (M2 (least-repeated-square (acl2::mod-expt-fast n
             ;;                                                                  (mv-nth 0 (Q*2^S (- p 1))) p)
             ;;                                             (mv-nth 1 (Q*2^S (- p 1))) p)))
             ;;       (:instance hyps-true-T-S-aux
             ;;                  (n n)
             ;;                  (p p)
             ;;                  (z z)
             ;;                  (M (mv-nth 1 (Q*2^S (- p 1))))
             ;;                  (Q (mv-nth 0 (Q*2^S (- p 1))))
             ;;                  (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
             ;;                  (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
             ;;                  (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
             ;;                  (M2 (least-repeated-square (acl2::mod-expt-fast n
             ;;                                                                  (mv-nth 0 (Q*2^S (- p 1))) p)
             ;;                                             (mv-nth 1 (Q*2^S (- p 1))) p)))
             
             
             
             ;:induct (T-S-AUX-= n M c tt R p)
             ;; (MV-NTH 1 (Q*2^S (+ -1 P)))
             ;; (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
             ;;                 P)
             ;; (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
             ;;                  P)
             ;; (ACL2::MOD-EXPT-FAST N
             ;;                 (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
             ;;                 P)
             ;; p)
             :in-theory (e/d (T-S-AUX-=
                              tonelli-shanks-has-sqrt-= acl2::mod-expt-fast)
                             (least-repeated-square))
             )
            ("Subgoal *1/2.5"
             :use (:instance sub*1/2.5 (z z) (p p)))
            
            )
    )
  )

          
(encapsulate
  ()

  (local
   (defthm T-s-aux-=T-s-aux
     (implies (posp n)
              (equal (T-S-aux-= n M c tt R p)
                     (T-S-aux M c tt R p)))
     :hints (("Goal"
              :in-theory (e/d (T-s-aux-=) (least-repeated-square))
              ))
     )
   )         
  (defthm tonelli-shanks-has-sqrt-=tshs
    (implies (and (natp n)
                  (natp p)
                  (natp z)
                  (> p 2)
                  (< z p)
                  (rtl::primep p)
                  (< n p)
                  (has-square-root? n p)
                  (not (has-square-root? z p)))
             (equal (tonelli-shanks-has-sqrt n p z)
                    (tonelli-shanks-has-sqrt-= n p z)))
    :hints (("Goal"
             :use (:instance T-s-aux-=T-s-aux (n n)
                             (M (MV-NTH 1 (Q*2^S (+ -1 P))))
                             (c (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
                                                     P))
                             (tt (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
                                                      P))
                             (R (ACL2::MOD-EXPT-FAST N
                                                     (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
                                                     P))
                             (p p))
             :in-theory (e/d (tonelli-shanks-has-sqrt tonelli-shanks-has-sqrt-=
                                                      T-s-aux-= T-S-aux)
                             (least-repeated-square))
             ))
    )
  )

--

(defun tonelli-shanks-has-sqrt-=-inv (n z S M c tt R p)
;:returns (yes/no booleanp)
  ;; low^2 <= x /\ x < high^2
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

       (posp S);; M = S
       (equal (mod (expt z (expt 2 (- M 1))) p) (mod -1 p)) ;; c = (acl2::mod-expt-fast z Q p)
;variables don't change                

       (natp c) ; (acl2::mod-expt-fast z Q p)
       (natp tt) ; (acl2::mod-expt-fast n Q p)
       (natp R) ; (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)
       (< M 0)
       (posp M)
       (equal (mod (* R R) p) (mod (* tt n) p))
       (= (acl2::mod-expt-fast tt (expt 2 (least-repeated-square tt M p)) p)
          1))
  )

(skip-proofs
 (defthm tonelli-shanks-is-sqrt-modp-sub4
   (IMPLIES
    (AND
     (< 0 (MV-NTH 1 (Q*2^S (+ -1 P))))
     (NOT
      (EQUAL
       (ACL2::MOD-EXPT-FAST (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
                                                 P)
                            1 P)
       1))
     (< 1 (MV-NTH 1 (Q*2^S (+ -1 P))))
     (EQUAL
      (ACL2::MOD-EXPT-FAST (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
                                                P)
                           2 P)
      1)
     (INTEGERP N)
     (<= 0 N)
     (<= 0 P)
     (INTEGERP Z)
     (<= 0 Z)
     (< 2 P)
     (< Z P)
     (RTL::PRIMEP P)
     (NOT (EQUAL Z 0))
     (NOT (EQUAL (ACL2::MOD-EXPT-FAST Z (+ -1/2 (* 1/2 P))
                                      P)
                 1))
     (NOT (EQUAL N 0))
     (NOT
      (EQUAL
       (MOD (* (ACL2::MOD-EXPT-FAST N
                                    (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
                                    P)
               (EXPT (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
                                          P)
                     (EXPT 2 (+ -2 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
            P)
       0)))
    (EQUAL
     (MOD
      (*
       (MOD (* (ACL2::MOD-EXPT-FAST N
                                    (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
                                    P)
               (EXPT (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
                                          P)
                     (EXPT 2 (+ -2 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
            P)
       (MOD (* (ACL2::MOD-EXPT-FAST N
                                    (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
                                    P)
               (EXPT (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
                                          P)
                     (EXPT 2 (+ -2 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
            P))
      P)
     N))
   )
 )

(defthm tonelli-shanks-is-sqrt-modp
  (implies (and (natp n)
                (natp p)
                (natp z)
                (> p 2)
                (< z p)
                (rtl::primep p)
                (not (has-square-root? z p))
                (equal (tonelli-shanks-has-sqrt-= n p z) y)
                (not (= y 0)))
           (= (mod (* y y) p) n))
  :hints (("Goal"
           
           :use (:instance T-S-AUX-= (n n) (z z) (S (MV-NTH 1 (Q*2^S (+
                                                                      -1 P))))
                           (M (MV-NTH 1 (Q*2^S (+ -1 P))))
                           (c (ACL2::MOD-EXPT-FAST Z (MV-NTH 0 (Q*2^S (+ -1 P)))
                                                   P))
                           (tt (ACL2::MOD-EXPT-FAST N (MV-NTH 0 (Q*2^S (+ -1 P)))
                                                    P))
                           (R (ACL2::MOD-EXPT-FAST N
                                                   (+ 1/2 (* 1/2 (MV-NTH 0 (Q*2^S (+ -1 P)))))
                                                   P))
                           (p p))
           :in-theory (e/d (T-S-AUX-=
                            tonelli-shanks-has-sqrt-=)
                           ())
           ))
  )

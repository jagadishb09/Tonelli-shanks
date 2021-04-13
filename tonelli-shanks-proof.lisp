
(in-package "PRIMES")

(include-book "kestrel/number-theory/tonelli-shanks-test" :dir :system)

(local
 (encapsulate
   ()
   (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))

   (defthm mod-of-expt-of-mod
     (implies (and (natp i)
                   (integerp x)
                   (posp y))
              (equal (mod (expt (mod x y) i) y)
                     (mod (expt x i) y))))

   (defthm mod-of-*-of-expt-of-mod
     (implies (and (natp i)
                   (integerp x1)
                   (integerp x2)
                   (posp y))
              (equal (mod (* x1 (expt (mod x2 y) i)) y)
                     (mod (* x1 (expt x2 i)) y))))

   (defthm natp-2^x
     (implies (natp x)
              (natp (expt 2 x)))
     )
   ))

(local
 (encapsulate
   ()
   
   (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
   (local (include-book "arithmetic/equalities" :dir :system))

   (defthm exponents-add-for-nonneg-exponents
     (implies (and (<= 0 i)
                   (<= 0 j)
                   (integerp i)
                   (integerp j))
              (equal 
               (* (expt r i)
                  (expt r j)) (expt r (+ i j)))))

   (defthm expt-half-linear
     (implies (natp i)
              (equal (+ (expt 2 (+ -1 i))
                        (expt 2 (+ -1 i)))
                     (expt 2 i))))

   (defthm exponents-multiply
     (implies (and (integerp i)
                   (integerp j))
              (equal (expt (expt r i) j)
                     (expt r (* i j)))))

   (defthm posp!=0
     (implies (posp x)
              (not (= x 0))))
   ))


(local
 (encapsulate
   ()
   (local
    (defthm lrs-aux-lemma-1
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< 2 p)
                    (< i m)
                    (< (+ i 1) m)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0))
               (equal (least-repeated-square-aux (+ i 1) tt^2^i m p) 0))))

   (local
    (defthm lrs-aux-lemma-2
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< 2 p)
                    (< i m)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0))
               (equal (least-repeated-square-aux (- m 1) tt^2^i m p) 0))
      :hints (("Goal"
               :use ((:instance LEAST-REPEATED-SQUARE-AUX (i m)
                                (tt^2^i (MOD (* TT^2^I TT^2^I) P))
                                (m m)
                                (p p)))
               :do-not-induct t
               ))))

   (local
    (defthm lrs-aux-lemma-3
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< 2 p)
                    (< i m)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0)
                    (>= x i)
                    (<= x (- m 1)))
               (equal (least-repeated-square-aux x tt^2^i m p) 0))))

   (local
    (defthm lrs-aux-lemma-4-1
      (IMPLIES (AND (INTEGERP I)
                    (< 0 I)
                    (INTEGERP M)
                    (<= 0 M)
                    (< I M)
                    (NOT (EQUAL (MOD (* TT^2^I TT^2^I) P) 1))
                    (NOT (EQUAL (MOD (EXPT (* TT^2^I TT^2^I)
                                           (EXPT 2 (+ -1 (- I) M)))
                                     P)
                                1))
                    (INTEGERP TT^2^I)
                    (<= 0 TT^2^I)
                    (INTEGERP P)
                    (<= 0 P)
                    (< 2 P)
                    (EQUAL (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                      (MOD (* TT^2^I TT^2^I) P)
                                                      M P)
                           0))
               (NOT (EQUAL (MOD (EXPT TT^2^I (EXPT 2 (+ (- I) M)))
                                P)
                           1)))
      :hints (("Goal"
               :use ((:instance exponents-multiply (i 2) (j (EXPT 2 (+ -1 (- I) M)))
                                (r tt^2^i))
                     (:instance exponents-add-for-nonneg-exponents (r 2) (i 1)
                                (j (+ -1 (- I) M))))
               ))))

   (local
    (defthm lrs-aux-lemma-4
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< i m)
                    (< 2 p)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0))
               (not (equal (mod (expt tt^2^i (expt 2 (- m i))) p) 1)))))

   (encapsulate
     ()

     (local (include-book "arithmetic-5/top" :dir :system))

     (defthmd least-repeated-square-aux-lemma5
       (implies (and (natp tt^2^i)
                     (posp i)
                     (natp m)
                     (natp p)
                     (< i m)
                     (< 2 p)
                     (equal (least-repeated-square-aux 1 tt^2^i m p) 0))
                (not (equal (mod (expt tt^2^i (expt 2 i)) p) 1)))
       :hints (("Goal"
                :use ((:instance lrs-aux-lemma-3 (tt^2^i tt^2^i)
                                 (i i)
                                 (m m)
                                 (p p)
                                 (x (- m i)))
                      (:instance lrs-aux-lemma-4 (tt^2^i tt^2^i)
                                 (i (- m i))
                                 (m m)
                                 (p p)))
                ))))
   ))

(local
 (encapsulate
   ()

   (local (include-book "rtl/rel11/lib/basic" :dir :system))
   (local (include-book "arithmetic/equalities" :dir :system))
   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm mod-*a-b=
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (= c 0)))
              (= (mod (* a b) c)
                 (mod (* (mod a c) (mod b c)) c))))

   (defthm mod-*mod-a*mod-b=
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (= c 0)))
              (= (mod (* (mod a c) (mod b c)) c)
                 (mod (* a b) c)))
     :hints (("Goal"
              :use (:instance mod-*a-b= (a a) (b b) (c c))
              :in-theory nil
              )))

   (defthm mod-times-mod
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (zp n))
                   (= (mod a n) (mod b n)))
              (= (mod (* a c) n) (mod (* b c) n)))
     :hints (("Goal"
              :use (:instance rtl::mod-times-mod (a a) (b b) (c c) (n n))
              :in-theory nil
              )))
   ))

(local
 (encapsulate
   ()
   (local (include-book "kestrel/number-theory/divides" :dir :system))
   (local (include-book "kestrel/crypto/ecurve/primes" :dir :system))
   
   (defthm primep-implies
     (implies (and (rtl::primep p)
                   (< 2 p))
              (and (oddp p)
                   (integerp p)))
     :hints (("goal"
              :in-theory (e/d (rtl::primep) (oddp))
              ))
     )
   ))

(encapsulate
  ()
  
  (local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm y^2=1modp-lemma1
     (implies (and (integerp a)
                   (integerp b)
                   (rtl::primep p)
                   (rtl::divides p (* a b))
                   (not (rtl::divides p b)))
              (rtl::divides p a))
     :hints (("goal"
              :use (:instance rtl::euclid (p p) (a a) (b b))
              ))))

  (local
   (defthm y^2=1modp-1
     (implies (and (rtl::primep p)
                   (integerp y)
                   (< 2 p)
                   (equal (mod (* y y) p) 1))
              (or (equal (mod y p) 1)
                  (equal (mod y p) (mod -1 p))))
     :hints (("goal"
              :cases ((rtl::divides p (- y 1))
                      (rtl::divides p (+ y 1)))
              :use ((:instance rtl::divides-mod-equal (n p) (a (* y y)) (b 1))
                    (:instance y^2=1modp-lemma1 (a (- y 1)) (b (+ y 1)))         
                    (:instance rtl::divides-mod-equal (n p) (a y) (b 1))
                    (:instance rtl::divides-mod-equal (n p) (a y) (b -1)))
              :in-theory (e/d (rtl::primep) ())
              ))))

  (local
   (defthm y^2=1modp-2
     (implies (and (rtl::primep p)
                   (integerp y)
                   (< 2 p)
                   (or (equal (mod y p) 1)
                       (equal (mod y p) (mod -1 p))))
              (equal (mod (* y y) p) 1))
     :hints (("goal"
              :cases ((equal (mod y p) 1)
                      (equal (mod y p) (mod -1 p)))
              :use ((:instance primep-implies (p p))
                    (:instance mod-*a-b= (a y) (b y) (c p))
                    (:instance mod-*mod-a*mod-b= (a y) (b y) (c p)))
              :in-theory (e/d () (mod))
              ))))

  (defthm y^2=1modp
    (implies (and (rtl::primep p)
                  (integerp y)
                  (< 2 p))
             (iff (equal (mod (* y y) p) 1)
                  (or (equal (mod y p) 1)
                      (equal (mod y p) (mod -1 p)))))
    :hints (("goal"
             :use ((:instance y^2=1modp-1)
                   (:instance y^2=1modp-2))
             )))
  )

(encapsulate
  ()

  (local (include-book "kestrel/arithmetic-light/expt" :dir :system))

  (local
   (defthmd least-repeated-square-aux-lemma1
     (implies (and (posp i)
                   (< i m)
                   (natp x)
                   (< x i)
                   (natp tt^2^i)
                   (natp m)
                   (natp p)
                   (< 2 p)
                   (not (equal (least-repeated-square-aux i
                                                          tt^2^i
                                                          m p)
                               0)))
              (< x (least-repeated-square-aux i
                                              tt^2^i
                                              m p)))
     :hints (("goal"
              :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
              ))))
  
  (local
   (defthm least-repeated-square-aux-lemma2
     (implies
      (and (integerp i)
           (<= 0 i)
           (integerp m)
           (<= 0 m)
           (< i m)
           (not (equal (mod (* tt tt) p) 1))
           (equal (mod (expt (mod (* tt tt) p)
                             (expt 2
                                   (+ (- i)
                                      (least-repeated-square-aux (+ 1 i)
                                                                 (mod (* tt tt) p)
                                                                 m p))))
                       p)
                  1)
           (< (+ 1 i) m)
           (integerp tt)
           (<= 0 tt)
           (< 0 m)
           (integerp p)
           (<= 0 p)
           (< 0 i)
           (< 2 p)
           (not (equal (least-repeated-square-aux (+ 1 i)
                                                  (mod (* tt tt) p)
                                                  m p)
                       0)))
      (equal (mod (expt tt
                        (expt 2
                              (+ 1 (- i)
                                 (least-repeated-square-aux (+ 1 i)
                                                            (mod (* tt tt) p)
                                                            m p))))
                  p)
             1))
     :hints (("goal"
              :use (
                    (:instance expt-half-linear (i (+ (- i)
                                                      (least-repeated-square-aux (+ 1 i)
                                                                                 (mod (* tt tt) p)
                                                                                 m p) 1)))
                    (:instance least-repeated-square-aux-lemma1 (i (+ i 1)) (x i)
                               (m m) (p p) (tt^2^i (mod (* tt tt) p))))
              :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
              ))))

  (defthmd least-repeated-square-aux-lemma3
    (implies (and (natp tt)
                  (posp m)
                  (natp p)
                  (posp i)
                  (< 2 p)
                  (equal (least-repeated-square-aux i tt m p) lrs)
                  (not (= lrs 0)))
             (and (= (mod (expt tt (expt 2 (+ lrs (- i) 1))) p) 1)
                  (< lrs m)
                  (< i m)))
    :hints (("goal"
             :use ((:instance least-repeated-square-aux-lemma2))
             :in-theory (e/d (acl2::expt) (y^2=1modp primep-implies
                                                     mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
             )))
  
  (local
   (defthmd least-repeated-square-aux-lemma4
     (implies (and (natp tt)
                   (natp m)
                   (natp p)
                   (< 2 p)
                   (equal (least-repeated-square-aux 1 tt m p) lrs)
                   (not (= lrs 0)))
              (and (= (mod (expt tt (expt 2 lrs)) p) 1)
                   (< lrs m)
                   (< 0 m)))
     :hints (("goal"
              :use (:instance least-repeated-square-aux-lemma3 (i 1) (tt tt) (m m)
                              (p p) (lrs (least-repeated-square-aux 1 tt m p)))
              :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies
                                                               mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))))
     ))
  
  (defthm least-repeated-square-equiv
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square tt m p) lrs)
                  (not (= lrs 0)))
             (= (mod (expt tt (expt 2 lrs)) p) 1))
    :hints (("Goal"
             :use ((:instance least-repeated-square-aux-lemma4 (tt tt) (m m) (p p)
                              (lrs (least-repeated-square-aux 1 tt m p))))
             :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
             )))

  (defthm least-repeated-square-tt^2^lrs=1
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (natp i)
                  (< i m)
                  (< 2 p)
                  (< 0 m)
                  (= (mod (expt tt (expt 2 i)) p) 1))
             (= (mod (expt tt (expt 2 (least-repeated-square tt m p))) p) 1))
    :hints (("goal"
             :use (
                   (:instance least-repeated-square-aux-lemma3
                              (tt tt) (m m) (p p) (lrs i) (i i))
                   (:instance least-repeated-square-aux-lemma5
                              (tt^2^i tt) (m m) (p p) (i i))
                   (:instance least-repeated-square-aux-lemma4
                              (tt tt) (m m) (p p)
                              (lrs (least-repeated-square-aux 1 tt m p)))
                   )
             :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
             )))         
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm least-repeated-square-aux-is-least
     (implies (and (natp tt)
                   (natp m)
                   (natp p)
                   (< 2 p)
                   (equal (least-repeated-square-aux i tt m p) d)
                   (not (= d 0))
                   (posp i)
                   (< i d))
              (not (= (mod (expt tt (expt 2 (- d i))) p) 1)))
     :hints (("goal"
              :use (
                    (:instance exponents-multiply
                               (i 2)
                               (j (EXPT 2 (+ -1 (- I) (LEAST-REPEATED-SQUARE-AUX (+ 1 I) (MOD (* TT TT) P) M P))))
                               (r tt))
                    (:instance exponents-add-for-nonneg-exponents (i 1)
                               (r 2)
                               (j (EXPT 2 (+ -1 (- I) (LEAST-REPEATED-SQUARE-AUX (+ 1 I)
                                                                                 (MOD (* TT TT) P) M P)))))       
                    (:instance least-repeated-square-aux-lemma3 (tt tt) (m m) (p p)
                               (i i) (lrs (least-repeated-square-aux i tt m p))))
              :in-theory (e/d (acl2::mod-expt-fast) (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
              ))))

  (defthm least-repeated-square-is-least
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square tt m p) d)
                  (not (= d 0)))
             (not (= (mod (expt tt (expt 2 (- d 1))) p) 1)))
    :hints (("Goal"
             :use (:instance least-repeated-square-aux-is-least
                             (i 1) (tt tt) (m m) (p p) (d (least-repeated-square-aux 1 tt m p)))
             )))
  )

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
   (local (include-book "kestrel/number-theory/divides" :dir :system))
   (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))

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
                    )
              :in-theory (enable acl2::mod-expt-fast rtl::primep)
              )))
   
   (local
    (defthm lemma-1
      (implies (and (integerp a)
                    (integerp b)
                    (integerp c))
               (equal (expt a (* b (expt 2 (- c 1))))
                      (expt a (/ (* b (expt 2 c)) 2))))))

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
                    (:instance posp!=0 (x (MV-NTH 1 (Q*2^S (+ -1 P)))))
                    (:instance exponents-multiply
                               (r z)
                               (i (MV-NTH 0 (Q*2^S (+ -1 P))))
                               (j (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                    )
              :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
              )))

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
                    (:instance posp!=0 (x (MV-NTH 1 (Q*2^S (+ -1 P)))))
                    (:instance exponents-multiply
                               (r z)
                               (i (MV-NTH 0 (Q*2^S (+ -1 P))))
                               (j (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                    )
              :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
              )))
   ))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
   (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))
   
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
              (and (posp M)
                   (natp c)
                   (natp tt)
                   (natp R)
                   (equal (mod (* R R) p) (mod (* tt n) p))
                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                   (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1)))
     :hints (("Goal"
              :use ((:instance least-repeated-square-tt^2^lrs=1
                               (m M)
                               (i (- M 1))
                               (p p))
                    (:instance posp-Q*2^S-n-is-even (n (- p 1)))
                    (:instance posp!=0 (x (MV-NTH 1 (Q*2^S (+ -1 P)))))
                    (:instance mod-of-expt-of-mod (x (EXPT N (MV-NTH 0 (Q*2^S (+ -1 P)))))
                               (y p)
                               (i (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                    (:instance mod-of-expt-of-mod (x (EXPT Z (MV-NTH 0 (Q*2^S (+ -1 P)))))
                               (y p)
                               (i (EXPT 2 (+ -1 (MV-NTH 1 (Q*2^S (+ -1 P)))))))
                    (:instance T-S-aux-z-is-non-residue (z z) (p p))
                    (:instance T-S-aux-n-is-residue (n n) (p p))
                    (:instance q2s-is-correct (n (- p 1))))
              :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) (y^2=1modp mod-*a-b= mod-*mod-a*mod-b= least-repeated-square mod-times-mod))
              :do-not-induct t
              )))))

(local
 (encapsulate
   ()

   (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
   (local (include-book "arithmetic/equalities" :dir :system))
   (local (include-book "arithmetic-5/top" :dir :system))

   (local
    (defthm repeated-square-=mod-expt-fast-*1/3
      (implies (posp a)
               (equal (* (expt c (expt 2 (+ -1 a)))
                         (expt c (expt 2 (+ -1 a))))
                      (expt c (expt 2 a))))
      :hints (("Goal"
               :use ((:instance acl2::exponents-add-for-nonneg-exponents
                                (r c)
                                (i (EXPT 2 (+ -1 a)))
                                (j (EXPT 2 (+ -1 a)))))
               ))))
   
   (defthm repeated-square-equiv
     (implies (and (posp x)
                   (natp c)
                   (natp p)
                   (< 2 p))
              (equal (repeated-square c x p)
                     (acl2::mod-expt-fast c (expt 2 x) p)))
     :hints (("Goal"
              :use ((:instance acl2::mod-of-expt-of-mod (i (EXPT 2 (+ -1 X)))
                               (x (* c c))
                               (y p))
                    (:instance acl2::exponents-add-unrestricted (r c)
                               (i (EXPT 2 (+ -1 X))) (j (EXPT 2 (+ -1 X)))))
              :in-theory (enable acl2::mod-expt-fast repeated-square)
              )))))
(local
 (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))
   
   (local
    (encapsulate
      ()

      (local (include-book "arithmetic-5/top" :dir :system))

      (defthm lemma1
        (implies (and (posp m)
                      (posp lrs)
                      (< lrs m))
                 (>= (+ -1 m (- lrs)) 0)))
      
      (defthm lemma2
        (implies (and (integerp c)
                      (natp m))
                 (integerp (expt c (expt 2 m)))))

      (defthm lemma3
        (implies (and (integerp a)
                      (integerp b)
                      (equal a (+ 1 b)))
                 (equal (- a 1) b)))))
   
   (defthmd t-s-aux-invariant1
     (implies (and (posp n)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (posp M)
                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                   (natp c)
                   (natp tt)
                   (natp R)
                   (equal (mod (* R R) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt M p) M2)
                   (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
              (if (zp M2)
                  (equal (mod (* R R) p) (mod n p))
                (let ((b (repeated-square c (- (- M M2) 1) p)))
                  (let ((c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (R2 (mod (* R b) p)))
                    (declare (ignore R2 tt2))
                    (equal (mod (expt c2 (expt 2 (- M2 1))) p) (mod -1 p))
                    ))))
     :hints (("Goal"
              :cases ((= (- (- M M2) 1) 0))
              :use ((:instance repeated-square-equiv (x (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))) (p p) (c c))
                    (:instance lemma1 (m m) (lrs (least-repeated-square tt m p)))
                    (:instance mod-*a-b= (a n) (b tt) (c p))
                    (:instance natp-2^x (x (+ -1 M (- (LEAST-REPEATED-SQUARE TT M P)))))
                    (:instance exponents-add-for-nonneg-exponents
                               (r c)
                               (i (EXPT 2
                                        (+ -1
                                           M (- (LEAST-REPEATED-SQUARE TT M P)))))
                               (j (EXPT 2
                                        (+ -1
                                           M (- (LEAST-REPEATED-SQUARE TT M P))))))
                    (:instance expt-half-linear (i  (+ M (- (LEAST-REPEATED-SQUARE TT M P)))))
                    
                    (:instance mod-*mod-a*mod-b=
                               (a (EXPT C
                                        (EXPT 2
                                              (+ -1
                                                 M (- (LEAST-REPEATED-SQUARE TT M P))))))
                               (b (EXPT C
                                        (EXPT 2
                                              (+ -1
                                                 M (- (LEAST-REPEATED-SQUARE TT M P))))))
                               (c p))
                    (:instance least-repeated-square-less-than-M (m m) (tt tt) (p p)))
              :in-theory (e/d (acl2::mod-expt-fast repeated-square) (y^2=1modp mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1 mod-times-mod))
              :do-not-induct t
              )))))

(local
 (encapsulate
   ()

   (local
    (encapsulate
      ()
      (local (include-book "arithmetic-5/top" :dir :system))
      

      (defthm lemma1
        (implies (and (natp tt)
                      (posp m)
                      (natp c)
                      (rtl::primep p)
                      (< 2 p))
                 (natP (MOD (* TT
                               (EXPT C
                                     (EXPT 2
                                           (+ -1
                                              M (- (LEAST-REPEATED-SQUARE TT M P)))))
                               (EXPT C
                                     (EXPT 2
                                           (+ -1
                                              M (- (LEAST-REPEATED-SQUARE TT M P))))))
                            P))))

      (defthm lemma2
        (implies (and (integerp a)
                      (integerp b)
                      (< a b))
                 (<= (+ a 1) b)))

      (defthm lemma3
        (implies (and (natp tt)
                      (posp m)
                      (natp c)
                      (rtl::primep p)
                      (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                      (< 2 p))
                 (EQUAL
                  (MOD
                   (EXPT (MOD (* TT
                                 (EXPT C
                                       (EXPT 2
                                             (+ -1
                                                M (- (LEAST-REPEATED-SQUARE TT M P)))))
                                 (EXPT C
                                       (EXPT 2
                                             (+ -1
                                                M (- (LEAST-REPEATED-SQUARE TT M P))))))
                              P)
                         (EXPT 2
                               (+ -1 (LEAST-REPEATED-SQUARE TT M P))))
                   P)
                  1))
        :hints (("Goal"
                 :use ((:instance least-repeated-square-is-least
                                  (tt tt) (m m) (p p)
                                  (d (LEAST-REPEATED-SQUARE TT M P)))
                       (:instance lemma2 (a (LEAST-REPEATED-SQUARE TT M P)) (b m))
                       (:instance y^2=1modp (y (EXPT TT
                                                     (EXPT 2
                                                           (+ -1 (LEAST-REPEATED-SQUARE TT M P))))))
                       (:instance mod-*mod-a*mod-b= (a -1) (b -1) (c p))
                       (:instance mod-*a-b= (c p)
                                  (a (EXPT C (EXPT 2 (+ -1 M))))
                                  (b (EXPT TT
                                           (EXPT 2
                                                 (+ -1 (LEAST-REPEATED-SQUARE TT M P)))))))
                 :in-theory (e/d (acl2::mod-expt-fast repeated-square) (y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-tt^2^lrs=1)))))

      (defthm lemma4
        (implies (and (posp m)
                      (posp lrs)
                      (< lrs m))
                 (>= (+ -1 m (- lrs)) 0)))
      
      (defthm lemma5
        (implies (and (integerp c)
                      (natp m))
                 (integerp (expt c (expt 2 m)))))

      (defthm lemma6
        (implies (integerp x)
                 (equal (* 1/2 (expt 2 x))
                        (expt 2 (- x 1)))))
      
      ))

   (local
    (defthmd t-s-aux-invariant2-lemma1
      (implies (and (posp n)
                    (< 2 p)
                    (rtl::primep p)
                    (< n p)
                    (has-square-root? n p)
                    (posp M)
                    (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                    (natp c)
                    (natp tt)
                    (natp R)
                    (equal (mod (* R R) p) (mod (* tt n) p))
                    (equal (least-repeated-square tt M p) M2)
                    (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
               (if (zp M2)
                   (equal (mod (* R R) p) (mod n p))
                 (let ((b (expt c (expt 2 (- (- M M2) 1)))))
                   (let ((c2 (mod (* b b) p))
                         (tt2 (mod (* tt b b) p))
                         (R2 (mod (* R b) p)))
                     (declare (ignore R2 c2))
                     (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)))))
      :hints (("Goal"
               :use (
                     (:instance least-repeated-square-tt^2^lrs=1
                                (tt (mod (* tt (expt c (expt 2 (- (- M (least-repeated-square tt M p)) 1)))
                                            (expt c (expt 2 (- (- M (least-repeated-square tt M p)) 1)))) p))
                                (m (least-repeated-square tt M p))
                                (p p)
                                (i (- (least-repeated-square tt M p) 1)))
                     (:instance mod-*a-b= (a n) (b tt) (c p))
                     (:instance least-repeated-square-less-than-M (tt tt) (m m) (p p))
                     (:instance least-repeated-square-is-least
                                (tt tt) (m m) (p p)
                                (d (LEAST-REPEATED-SQUARE TT M P)))
                     (:instance lemma2 (a (LEAST-REPEATED-SQUARE TT M P)) (b m))
                     (:instance y^2=1modp (y (EXPT TT
                                                   (EXPT 2
                                                         (+ -1 (LEAST-REPEATED-SQUARE TT M P))))))
                     (:instance mod-*mod-a*mod-b= (a -1) (b -1) (c p))
                     (:instance mod-*a-b= (c p)
                                (a (EXPT C (EXPT 2 (+ -1 M))))
                                (b (EXPT TT
                                         (EXPT 2
                                               (+ -1 (LEAST-REPEATED-SQUARE TT M P)))))))
               :in-theory (e/d (acl2::mod-expt-fast) ( repeated-square y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1))
               :do-not-induct t
               )
              )))

   (local
    (encapsulate
      ()

      (local (include-book "arithmetic-5/top" :dir :system))
      (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
      (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
      (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

      (defthmd t-s-aux-invariant2-lemma2
        (implies (and (posp n)
                      (< 2 p)
                      (rtl::primep p)
                      (< n p)
                      (has-square-root? n p)
                      (posp M)
                      (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                      (natp c)
                      (natp tt)
                      (natp R)
                      (equal (expt c (expt 2 (- (- M M2) 1))) b1)
                      (equal (mod (* R R) p) (mod (* tt n) p))
                      (equal (least-repeated-square tt M p) M2)
                      (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
                 (if (zp M2)
                     (equal (mod (* R R) p) (mod n p))
                   (let ((b (repeated-square c (- (- M M2) 1) p)))
                     (let ((c2 (mod (* b b) p))
                           (tt2 (mod (* tt b b) p))
                           (R2 (mod (* R b) p)))
                       (declare (ignore R2 c2))
                       (equal tt2 (mod (* tt b1 b1) p))))))
        :hints (("Goal"
                 :use ((:instance lemma5 (c c) (m (- (- M M2) 1)))
                       (:instance lemma2 (a m2) (b m))
                       (:instance least-repeated-square-less-than-M (tt tt) (m m) (p p))
                       (:instance mod-*a-b= (a n) (b tt) (c p))
                       (:instance repeated-square-equiv (x (- (- M M2) 1)) (p p) (c c))
                       (:instance mod-of-*-of-expt-of-mod (i 2) (y p)
                                  (x1 tt) (x2 (expt c (expt 2 (- (- M M2) 1))))))
                 :in-theory
                 (e/d (acl2::mod-expt-fast repeated-square) (y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1))
                 :do-not-induct t
                 )))))
   
   (defthmd t-s-aux-invariant2
     (implies (and (posp n)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (posp M)
                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                   (natp c)
                   (natp tt)
                   (natp R)
                   (equal (mod (* R R) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt M p) M2)
                   (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
              (if (zp M2)
                  (equal (mod (* R R) p) (mod n p))
                (let ((b (repeated-square c (- (- M M2) 1) p)))
                  (let ((c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (R2 (mod (* R b) p)))
                    (declare (ignore R2 c2))
                    (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 M2 p)) p) 1)))))
     :hints (("Goal"
              :use ((:instance t-s-aux-invariant2-lemma2 (tt tt) (m m) (p p) (n n) (c c) (R R)
                               (m2 (least-repeated-square tt M p)) (b1 (expt c (expt 2 (- (- M M2) 1)))))
                    (:instance t-s-aux-invariant2-lemma1 (tt tt) (m m) (p p) (n n) (c c) (R R)
                               (m2 (least-repeated-square tt M p)))
                    )
              :in-theory
              (e/d (acl2::mod-expt-fast repeated-square) (y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1))
              :do-not-induct t
              )))

   (local
    (encapsulate
      ()
      (local (include-book "arithmetic-5/top" :dir :system))
      (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
      (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
      (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))
      
      (defthmd t-s-aux-invariant3-lemma1
        (implies (and (posp n)
                      (< 2 p)
                      (rtl::primep p)
                      (< n p)
                      (has-square-root? n p)
                      (posp M)
                      (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                      (natp c)
                      (natp tt)
                      (natp R)
                      (equal (mod (* R R) p) (mod (* tt n) p))
                      (equal (least-repeated-square tt M p) M2)
                      (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
                 (if (zp M2)
                     (equal (mod (* R R) p) (mod n p))
                   (let ((b (expt c (expt 2 (- (- M M2) 1)))))
                     (let ((c2 (mod (* b b) p))
                           (tt2 (mod (* tt b b) p))
                           (R2 (mod (* R b) p)))
                       (declare (ignore c2))
                       (equal (mod (* R2 R2) p) (mod (* tt2 n) p))))))
        :hints (("Goal"
                 :use ((:instance mod-times-mod (a (EXPT R 2)) (b (* N TT))
                                  (c (EXPT C (EXPT 2 (+ M (- (LEAST-REPEATED-SQUARE TT M P))))))
                                  (n p)))
                 :in-theory (e/d (acl2::mod-expt-fast repeated-square acl2::not-evenp-when-oddp) (y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1))
                 :do-not-induct t
                 )))))

   (defthmd t-s-aux-invariant3
     (implies (and (posp n)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (posp M)
                   (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                   (natp c)
                   (natp tt)
                   (natp R)
                   (equal (mod (* R R) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt M p) M2)
                   (= (acl2::mod-expt-fast tt (expt 2 M2) p) 1))
              (if (zp M2)
                  (equal (mod (* R R) p) (mod n p))
                (let ((b (repeated-square c (- (- M M2) 1) p)))
                  (let ((c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (R2 (mod (* R b) p)))
                    (declare (ignore c2))
                    (equal (mod (* R2 R2) p) (mod (* tt2 n) p))))))
     :hints (("Goal"
              :use ((:instance t-s-aux-invariant3-lemma1)
                    (:instance mod-of-*-of-expt-of-mod (i 1) (x2 (expt c (expt 2 (- (- M M2) 1))))
                               (x1 r) (y p))
                    (:instance repeated-square-equiv (x (- (- M M2) 1)) (p p) (c c))
                    (:instance t-s-aux-invariant2-lemma2 (tt tt) (m m) (p p) (n n) (c c) (R R)
                               (m2 (least-repeated-square tt M p)) (b1 (expt c (expt 2 (- (- M M2) 1))))))
              :in-theory (e/d (acl2::mod-expt-fast repeated-square) (y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1))
              :do-not-induct t
              )))))

(defthm t-s-aux-loop-invariants
  (implies  (and (posp n)
                 (has-square-root? n p)
                 (posp M)
                 (natp c)
                 (natp tt)
                 (natp R)
                 (natp p)
                 (< n p)
                 (rtl::primep p)
                 (< 2 p)
                 (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                 (= (acl2::mod-expt-fast tt (expt 2 (least-repeated-square tt m p)) p) 1)
                 (equal (mod (* R R) p) (mod (* tt n) p))
                 (< 0 (least-repeated-square tt M p)))
            (let ((b (repeated-square c (- (- M (least-repeated-square tt m p)) 1) p)))
              (let ((c2 (mod (* b b) p))
                    (tt2 (mod (* tt b b) p))
                    (R2 (mod (* R b) p)))
                (and (equal (mod (* R2 R2) p) (mod (* tt2 n) p))                       
                     (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 (least-repeated-square tt M p) p)) p) 1)
                     (equal (mod (expt c2 (expt 2 (- (least-repeated-square tt M p) 1))) p) (mod -1 p))
                     ))))
  :hints (("Goal"
           :use ((:instance t-s-aux-invariant1 (n n) (m m) (c c) (tt tt) (r r) (p p)
                            (m2 (least-repeated-square tt M p)))
                 (:instance t-s-aux-invariant2 (n n) (m m) (c c) (tt tt) (r r) (p p)
                            (m2 (least-repeated-square tt M p)))
                 (:instance t-s-aux-invariant3 (n n) (m m) (c c) (tt tt) (r r) (p p)
                            (m2 (least-repeated-square tt M p))))
           :in-theory (e/d (acl2::mod-expt-fast) (repeated-square y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux T-S-aux-n-is-residue T-S-aux-z-is-non-residue least-repeated-square-is-least least-repeated-square-tt^2^lrs=1))
           :do-not-induct t
           )))

(defthm t-s-aux-base-case
  (IMPLIES (AND (EQUAL (LEAST-REPEATED-SQUARE TT M P) 0)
                (INTEGERP N)
                (< 0 N)
                (RTL::PRIMEP P)
                (EQUAL (ACL2::MOD-EXPT-FAST N (+ -1/2 (* 1/2 P))
                                            P)
                       1)
                (INTEGERP M)
                (< 0 M)
                (INTEGERP C)
                (<= 0 C)
                (INTEGERP TT)
                (<= 0 TT)
                (INTEGERP R)
                (<= 0 R)
                (<= 0 P)
                (< N P)
                (< 2 P)
                (EQUAL (MOD (EXPT C (EXPT 2 (+ -1 M))) P)
                       (+ -1 P))
                (EQUAL (ACL2::MOD-EXPT-FAST TT 1 P) 1)
                (EQUAL (MOD (* R R) P)
                       (MOD (* N TT) P)))
           (EQUAL (MOD (* N TT) P) N))
  :hints (("Goal"
           :in-theory (e/d () (acl2::mod-expt-fast repeated-square y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux least-repeated-square-is-least least-repeated-square-tt^2^lrs=1 mod expt rtl::mod acl2::expt)) 
           :use (:instance t-s-aux-invariant3 (n n) (p p) (M M) (c c) (tt tt) (R R) (m2 (least-repeated-square tt m p))))))

(defthm T-S-aux-equiv
  (implies  (and (posp n)
                 (has-square-root? n p)
                 (posp M)
                 (natp c)
                 (natp tt)
                 (natp R)
                 (natp p)
                 (< n p)
                 (rtl::primep p)
                 (< 2 p)
                 (equal (mod (expt c (expt 2 (- M 1))) p) (mod -1 p))
                 (= (acl2::mod-expt-fast tt (expt 2 (least-repeated-square tt m p)) p) 1)
                 (equal (mod (* R R) p) (mod (* tt n) p)))
            (= (mod (* (T-S-AUX M c tt R p) (T-S-AUX M c tt R p)) p) n))
  :hints (("Goal"        
           :in-theory (e/d () (acl2::mod-expt-fast BINARY-* acl2::BINARY-* repeated-square y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux least-repeated-square-is-least least-repeated-square-tt^2^lrs=1 mod expt rtl::mod acl2::expt))          
           :induct (T-S-AUX M c tt R p)
           )))

(defthm tonelli-shanks-is-sqrt-modp
  (implies (and (natp n)
                (natp z)
                (> p 2)
                (has-square-root? n p)
                (< n p)
                (< z p)
                (rtl::primep p)
                (not (has-square-root? z p))
                (equal (tonelli-shanks-sqrt-aux n p z) y))
           (equal (mod (* y y) p) n))
  :hints (("Goal"
           :use ((:instance hyps-true-T-S-aux
                            (n n)
                            (p p)
                            (M (mv-nth 1 (Q*2^S (- p 1))))
                            (Q (mv-nth 0 (Q*2^S (- p 1))))
                            (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
                            (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
                            (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
                            (M2 (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p) (mv-nth 1 (Q*2^S (- p 1))) p)))
                 (:instance T-S-aux-equiv
                            (n n)
                            (p p)
                            (M (mv-nth 1 (Q*2^S (- p 1))))
                            (c (acl2::mod-expt-fast z (mv-nth 0 (Q*2^S (- p 1))) p))
                            (tt (acl2::mod-expt-fast n (mv-nth 0 (Q*2^S (- p 1))) p))
                            (R (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (Q*2^S (- p 1))) 1) 2) p))
                            )
                 )
           :in-theory (e/d (acl2::mod-expt-fast TONELLI-SHANKS-SQRT-AUX) (repeated-square y^2=1modp mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square hyps-true-T-S-aux least-repeated-square-is-least least-repeated-square-tt^2^lrs=1 )) 
           )))

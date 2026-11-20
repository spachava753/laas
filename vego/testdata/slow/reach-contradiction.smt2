; canReach's contradiction check of the path after the call of get in Fetch (errors.go canReach), at 35dca07: unknown at the limit, 4,001,754 units, 19 s. Without its quantified facts it is sat in 6,712 units.
(set-option :rlimit 4000000)
(declare-const c1 Int) ; brk
(assert (<= 1 c1))
(declare-datatype SeqInt ((SeqInt.mk (SeqInt.at (Array Int Int)) (SeqInt.raw Int))))
(define-fun SeqInt.len ((s SeqInt)) Int (ite (< (SeqInt.raw s) 0) 0 (SeqInt.raw s)))
(define-fun SeqInt.store ((s SeqInt) (i Int) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) i v) (SeqInt.raw s)))
(define-fun SeqInt.fill ((n Int) (v Int)) SeqInt (SeqInt.mk ((as const (Array Int Int)) v) n))
(define-fun SeqInt.push ((s SeqInt) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) (SeqInt.len s) v) (+ (SeqInt.len s) 1)))
(define-fun SeqInt.concat ((a SeqInt) (b SeqInt)) SeqInt (SeqInt.mk (lambda ((j Int)) (ite (< j (SeqInt.len a)) (select (SeqInt.at a) j) (select (SeqInt.at b) (- j (SeqInt.len a))))) (+ (SeqInt.len a) (SeqInt.len b))))
(define-fun SeqInt.sub ((s SeqInt) (lo Int) (hi Int)) SeqInt (SeqInt.mk (lambda ((j Int)) (select (SeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c2 SeqInt) ; $url
(assert (<= (SeqInt.len c2) 281474976710656))
(declare-const c3 Int) ; brk@1
(assert (<= c1 c3))
(declare-const c4 Int) ; get#ptr@1
(declare-const c5 Int) ; get#at@1
(assert (and (<= 0 c4) (< c4 c3) (<= 0 c5) (<= c5 281474976710656)))
(declare-const c6 SeqInt) ; home
(declare-datatype SeqSeqInt ((SeqSeqInt.mk (SeqSeqInt.at (Array Int SeqInt)) (SeqSeqInt.raw Int))))
(define-fun SeqSeqInt.len ((s SeqSeqInt)) Int (ite (< (SeqSeqInt.raw s) 0) 0 (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.store ((s SeqSeqInt) (i Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) i v) (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.fill ((n Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk ((as const (Array Int SeqInt)) v) n))
(define-fun SeqSeqInt.push ((s SeqSeqInt) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) (SeqSeqInt.len s) v) (+ (SeqSeqInt.len s) 1)))
(define-fun SeqSeqInt.concat ((a SeqSeqInt) (b SeqSeqInt)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqInt.len a)) (select (SeqSeqInt.at a) j) (select (SeqSeqInt.at b) (- j (SeqSeqInt.len a))))) (+ (SeqSeqInt.len a) (SeqSeqInt.len b))))
(define-fun SeqSeqInt.sub ((s SeqSeqInt) (lo Int) (hi Int)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c7 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Body
(define-fun t8 () Int (select (SeqInt.at (select (SeqSeqInt.at c7) c4)) (+ c5 64)))
(define-fun t9 () Int (select (SeqInt.at c6) t8))
(assert (and (<= 0 t9) (< t9 c3) (< 0 (select (SeqInt.at c6) t8))))
(declare-sort Err 0)
(declare-const nil Err)
(declare-const some-error Err)
(assert (not (= some-error nil)))
(declare-fun error-is (Err Err) Bool)
(declare-const c10 Err) ; get@1
(declare-datatype SeqBool ((SeqBool.mk (SeqBool.at (Array Int Bool)) (SeqBool.raw Int))))
(define-fun SeqBool.len ((s SeqBool)) Int (ite (< (SeqBool.raw s) 0) 0 (SeqBool.raw s)))
(define-fun SeqBool.store ((s SeqBool) (i Int) (v Bool)) SeqBool (SeqBool.mk (store (SeqBool.at s) i v) (SeqBool.raw s)))
(define-fun SeqBool.fill ((n Int) (v Bool)) SeqBool (SeqBool.mk ((as const (Array Int Bool)) v) n))
(define-fun SeqBool.push ((s SeqBool) (v Bool)) SeqBool (SeqBool.mk (store (SeqBool.at s) (SeqBool.len s) v) (+ (SeqBool.len s) 1)))
(define-fun SeqBool.concat ((a SeqBool) (b SeqBool)) SeqBool (SeqBool.mk (lambda ((j Int)) (ite (< j (SeqBool.len a)) (select (SeqBool.at a) j) (select (SeqBool.at b) (- j (SeqBool.len a))))) (+ (SeqBool.len a) (SeqBool.len b))))
(define-fun SeqBool.sub ((s SeqBool) (lo Int) (hi Int)) SeqBool (SeqBool.mk (lambda ((j Int)) (select (SeqBool.at s) (+ lo j))) (- hi lo)))
(declare-datatype SeqSeqBool ((SeqSeqBool.mk (SeqSeqBool.at (Array Int SeqBool)) (SeqSeqBool.raw Int))))
(define-fun SeqSeqBool.len ((s SeqSeqBool)) Int (ite (< (SeqSeqBool.raw s) 0) 0 (SeqSeqBool.raw s)))
(define-fun SeqSeqBool.store ((s SeqSeqBool) (i Int) (v SeqBool)) SeqSeqBool (SeqSeqBool.mk (store (SeqSeqBool.at s) i v) (SeqSeqBool.raw s)))
(define-fun SeqSeqBool.fill ((n Int) (v SeqBool)) SeqSeqBool (SeqSeqBool.mk ((as const (Array Int SeqBool)) v) n))
(define-fun SeqSeqBool.push ((s SeqSeqBool) (v SeqBool)) SeqSeqBool (SeqSeqBool.mk (store (SeqSeqBool.at s) (SeqSeqBool.len s) v) (+ (SeqSeqBool.len s) 1)))
(define-fun SeqSeqBool.concat ((a SeqSeqBool) (b SeqSeqBool)) SeqSeqBool (SeqSeqBool.mk (lambda ((j Int)) (ite (< j (SeqSeqBool.len a)) (select (SeqSeqBool.at a) j) (select (SeqSeqBool.at b) (- j (SeqSeqBool.len a))))) (+ (SeqSeqBool.len a) (SeqSeqBool.len b))))
(define-fun SeqSeqBool.sub ((s SeqSeqBool) (lo Int) (hi Int)) SeqSeqBool (SeqSeqBool.mk (lambda ((j Int)) (select (SeqSeqBool.at s) (+ lo j))) (- hi lo)))
(declare-const c11 SeqSeqBool) ; mem iface state
(assert (=> true (=> (= c10 nil) (and (not (= c4 0)) (not (= t8 0)) (not (select (SeqBool.at (select (SeqSeqBool.at c11) (select (SeqInt.at c6) (select (SeqInt.at (select (SeqSeqInt.at c7) c4)) (+ c5 64))))) (+ 2997695091990504928268101341469504234022244 0))) (<= c1 (select (SeqInt.at c6) (select (SeqInt.at (select (SeqSeqInt.at c7) c4)) (+ c5 64))))))))
(declare-datatype SeqSeqSeqInt ((SeqSeqSeqInt.mk (SeqSeqSeqInt.at (Array Int SeqSeqInt)) (SeqSeqSeqInt.raw Int))))
(define-fun SeqSeqSeqInt.len ((s SeqSeqSeqInt)) Int (ite (< (SeqSeqSeqInt.raw s) 0) 0 (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.store ((s SeqSeqSeqInt) (i Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) i v) (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.fill ((n Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk ((as const (Array Int SeqSeqInt)) v) n))
(define-fun SeqSeqSeqInt.push ((s SeqSeqSeqInt) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) (SeqSeqSeqInt.len s) v) (+ (SeqSeqSeqInt.len s) 1)))
(define-fun SeqSeqSeqInt.concat ((a SeqSeqSeqInt) (b SeqSeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqSeqInt.len a)) (select (SeqSeqSeqInt.at a) j) (select (SeqSeqSeqInt.at b) (- j (SeqSeqSeqInt.len a))))) (+ (SeqSeqSeqInt.len a) (SeqSeqSeqInt.len b))))
(define-fun SeqSeqSeqInt.sub ((s SeqSeqSeqInt) (lo Int) (hi Int)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c12 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Status
(define-fun t13 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c12) c4)) (+ c5 0)))
(declare-const c14 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.StatusCode
(define-fun t15 () Int (select (SeqInt.at (select (SeqSeqInt.at c14) c4)) (+ c5 16)))
(declare-const c16 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Proto
(define-fun t17 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c16) c4)) (+ c5 24)))
(declare-const c18 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMajor
(define-fun t19 () Int (select (SeqInt.at (select (SeqSeqInt.at c18) c4)) (+ c5 40)))
(declare-const c20 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMinor
(define-fun t21 () Int (select (SeqInt.at (select (SeqSeqInt.at c20) c4)) (+ c5 48)))
(declare-const c22 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Header
(define-fun t23 () Int (select (SeqInt.at (select (SeqSeqInt.at c22) c4)) (+ c5 56)))
(define-fun t24 () Int (select (SeqInt.at (select (SeqSeqInt.at c7) c4)) (+ c5 64)))
(define-fun t25 () Int (select (SeqInt.at c6) t24))
(declare-const c26 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ContentLength
(define-fun t27 () Int (select (SeqInt.at (select (SeqSeqInt.at c26) c4)) (+ c5 80)))
(declare-const c28 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#ref
(define-fun t29 () Int (select (SeqInt.at (select (SeqSeqInt.at c28) c4)) (+ c5 88)))
(declare-const c30 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#off
(define-fun t31 () Int (select (SeqInt.at (select (SeqSeqInt.at c30) c4)) (+ c5 88)))
(declare-const c32 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#len
(define-fun t33 () Int (select (SeqInt.at (select (SeqSeqInt.at c32) c4)) (+ c5 88)))
(declare-const c34 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#cap
(define-fun t35 () Int (select (SeqInt.at (select (SeqSeqInt.at c34) c4)) (+ c5 88)))
(declare-const c36 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Trailer
(define-fun t37 () Int (select (SeqInt.at (select (SeqSeqInt.at c36) c4)) (+ c5 120)))
(declare-const c38 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#ptr
(define-fun t39 () Int (select (SeqInt.at (select (SeqSeqInt.at c38) c4)) (+ c5 128)))
(declare-const c40 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#at
(define-fun t41 () Int (select (SeqInt.at (select (SeqSeqInt.at c40) c4)) (+ c5 128)))
(declare-const c42 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#ptr
(define-fun t43 () Int (select (SeqInt.at (select (SeqSeqInt.at c42) c4)) (+ c5 136)))
(declare-const c44 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#at
(define-fun t45 () Int (select (SeqInt.at (select (SeqSeqInt.at c44) c4)) (+ c5 136)))
(declare-const c49 SeqSeqInt) ; mem map map[string][]string#1#val#ref
(declare-const c50 SeqSeqInt) ; mem map map[string][]string#1#val#off
(declare-const c51 SeqSeqInt) ; mem map map[string][]string#1#val#len
(declare-const c52 SeqSeqInt) ; mem map map[string][]string#1#val#cap
(declare-const c54 SeqSeqSeqInt) ; mem elem string#2
(assert (and (<= 0 c4) (< c4 c3) (<= 0 c5) (<= c5 281474976710656) (<= (SeqInt.len t13) 281474976710656) (<= (- 9223372036854775808) t15) (<= t15 9223372036854775807) (<= (SeqInt.len t17) 281474976710656) (<= (- 9223372036854775808) t19) (<= t19 9223372036854775807) (<= (- 9223372036854775808) t21) (<= t21 9223372036854775807) (<= 0 t23) (< t23 c3) (<= 0 t25) (< t25 c3) (< 0 (select (SeqInt.at c6) t24)) (<= (- 9223372036854775808) t27) (<= t27 9223372036854775807) (<= 0 t29) (< t29 c3) (<= 0 t31) (<= 0 t33) (<= t33 t35) (<= (+ (* t31 16) (* t35 16)) 281474976710656) (<= (- 9223372036854775808) t35) (<= t35 9223372036854775807) (<= 0 t37) (< t37 c3) (<= 0 t39) (< t39 c3) (<= 0 t41) (<= t41 281474976710656) (<= 0 t43) (< t43 c3) (<= 0 t45) (<= t45 281474976710656) (forall ((b46 Int)) (=> (and (<= 0 b46) (< b46 (SeqInt.len t13))) (and (<= 0 (select (SeqInt.at t13) b46)) (<= (select (SeqInt.at t13) b46) 255)))) (forall ((b47 Int)) (=> (and (<= 0 b47) (< b47 (SeqInt.len t17))) (and (<= 0 (select (SeqInt.at t17) b47)) (<= (select (SeqInt.at t17) b47) 255)))) (forall ((b48 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c49) t23)) b48)) (< (select (SeqInt.at (select (SeqSeqInt.at c49) t23)) b48) c3) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c50) t23)) b48)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c51) t23)) b48)) (<= (select (SeqInt.at (select (SeqSeqInt.at c51) t23)) b48) (select (SeqInt.at (select (SeqSeqInt.at c52) t23)) b48)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c50) t23)) b48) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c52) t23)) b48) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c52) t23)) b48)) (<= (select (SeqInt.at (select (SeqSeqInt.at c52) t23)) b48) 9223372036854775807))) (and (forall ((b53 Int)) (=> (and (<= 0 b53) (< b53 t33)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c54) t29)) (+ (+ t31 (* b53 1)) 0))) 281474976710656))) (forall ((b56 Int)) (! (=> (and (<= 0 (+ b56 (- (+ t31 0)))) (< (+ b56 (- (+ t31 0))) t33)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c54) t29)) b56)) 281474976710656)) :pattern ((select (SeqSeqInt.at (select (SeqSeqSeqInt.at c54) t29)) b56))))) (forall ((b57 Int)) (=> (and (<= 0 b57) (< b57 t33)) (forall ((b58 Int)) (=> (and (<= 0 b58) (< b58 (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c54) t29)) (+ (+ t31 (* b57 1)) 0))))) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c54) t29)) (+ (+ t31 (* b57 1)) 0))) b58)) (<= (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c54) t29)) (+ (+ t31 (* b57 1)) 0))) b58) 255)))))) (forall ((b59 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c49) t37)) b59)) (< (select (SeqInt.at (select (SeqSeqInt.at c49) t37)) b59) c3) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c50) t37)) b59)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c51) t37)) b59)) (<= (select (SeqInt.at (select (SeqSeqInt.at c51) t37)) b59) (select (SeqInt.at (select (SeqSeqInt.at c52) t37)) b59)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c50) t37)) b59) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c52) t37)) b59) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c52) t37)) b59)) (<= (select (SeqInt.at (select (SeqSeqInt.at c52) t37)) b59) 9223372036854775807)))))
(assert true)
(assert (and (<= (SeqInt.len c2) 281474976710656) (forall ((b60 Int)) (=> (and (<= 0 b60) (< b60 (SeqInt.len c2))) (and (<= 0 (select (SeqInt.at c2) b60)) (<= (select (SeqInt.at c2) b60) 255))))))
(assert (and (<= (SeqInt.len c2) 281474976710656) (forall ((b61 Int)) (=> (and (<= 0 b61) (< b61 (SeqInt.len c2))) (and (<= 0 (select (SeqInt.at c2) b61)) (<= (select (SeqInt.at c2) b61) 255))))))
(check-sat-using (then simplify propagate-values ctx-simplify simplify elim-uncnstr smt))

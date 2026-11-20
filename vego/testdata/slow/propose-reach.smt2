; A proposal of canReach's search after the call of get in Fetch (errors.go proposeFor), at 35dca07: unknown at its limit, 1,001,978 units, 6.8 s. Without its quantified facts it is sat in 8,765 units.
(set-option :rlimit 1000000)
(declare-const c1 Int) ; sample 0
(assert (<= 0 c1))
(assert (<= c1 4096))
(declare-const c2 Int) ; sample 1
(assert (<= 0 c2))
(assert (<= c2 255))
(define-fun t3 () Bool (<= 1 1))
(assert t3)
(declare-datatype SeqInt ((SeqInt.mk (SeqInt.at (Array Int Int)) (SeqInt.raw Int))))
(define-fun SeqInt.len ((s SeqInt)) Int (ite (< (SeqInt.raw s) 0) 0 (SeqInt.raw s)))
(define-fun SeqInt.store ((s SeqInt) (i Int) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) i v) (SeqInt.raw s)))
(define-fun SeqInt.fill ((n Int) (v Int)) SeqInt (SeqInt.mk ((as const (Array Int Int)) v) n))
(define-fun SeqInt.push ((s SeqInt) (v Int)) SeqInt (SeqInt.mk (store (SeqInt.at s) (SeqInt.len s) v) (+ (SeqInt.len s) 1)))
(define-fun SeqInt.concat ((a SeqInt) (b SeqInt)) SeqInt (SeqInt.mk (lambda ((j Int)) (ite (< j (SeqInt.len a)) (select (SeqInt.at a) j) (select (SeqInt.at b) (- j (SeqInt.len a))))) (+ (SeqInt.len a) (SeqInt.len b))))
(define-fun SeqInt.sub ((s SeqInt) (lo Int) (hi Int)) SeqInt (SeqInt.mk (lambda ((j Int)) (select (SeqInt.at s) (+ lo j))) (- hi lo)))
(define-fun t4 () SeqInt (SeqInt.fill c1 c2))
(define-fun t5 () Bool (<= (SeqInt.len t4) 281474976710656))
(assert t5)
(assert true)
(define-fun t6 () Bool (<= (SeqInt.len t4) 281474976710656))
(assert t6)
(assert (forall ((b7 Int)) (=> (and (<= 0 b7) (< b7 (SeqInt.len t4))) (and (<= 0 c2) (<= c2 255)))))
(define-fun t8 () Bool (<= (SeqInt.len t4) 281474976710656))
(assert t8)
(assert (forall ((b9 Int)) (=> (and (<= 0 b9) (< b9 (SeqInt.len t4))) (and (<= 0 c2) (<= c2 255)))))
(assert t3)
(assert t5)
(declare-const c10 Int) ; brk@1
(assert (<= 1 c10))
(declare-const c11 Int) ; get#ptr@1
(declare-const c12 Int) ; get#at@1
(assert (and (<= 0 c11) (< c11 c10) (<= 0 c12) (<= c12 281474976710656)))
(declare-const c13 SeqInt) ; home
(declare-datatype SeqSeqInt ((SeqSeqInt.mk (SeqSeqInt.at (Array Int SeqInt)) (SeqSeqInt.raw Int))))
(define-fun SeqSeqInt.len ((s SeqSeqInt)) Int (ite (< (SeqSeqInt.raw s) 0) 0 (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.store ((s SeqSeqInt) (i Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) i v) (SeqSeqInt.raw s)))
(define-fun SeqSeqInt.fill ((n Int) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk ((as const (Array Int SeqInt)) v) n))
(define-fun SeqSeqInt.push ((s SeqSeqInt) (v SeqInt)) SeqSeqInt (SeqSeqInt.mk (store (SeqSeqInt.at s) (SeqSeqInt.len s) v) (+ (SeqSeqInt.len s) 1)))
(define-fun SeqSeqInt.concat ((a SeqSeqInt) (b SeqSeqInt)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqInt.len a)) (select (SeqSeqInt.at a) j) (select (SeqSeqInt.at b) (- j (SeqSeqInt.len a))))) (+ (SeqSeqInt.len a) (SeqSeqInt.len b))))
(define-fun SeqSeqInt.sub ((s SeqSeqInt) (lo Int) (hi Int)) SeqSeqInt (SeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c14 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Body
(define-fun t15 () Int (select (SeqInt.at (select (SeqSeqInt.at c14) c11)) (+ c12 64)))
(define-fun t16 () Int (select (SeqInt.at c13) t15))
(assert (and (<= 0 t16) (< t16 c10) (< 0 (select (SeqInt.at c13) t15))))
(declare-sort Err 0)
(declare-const nil Err)
(declare-const some-error Err)
(assert (not (= some-error nil)))
(declare-fun error-is (Err Err) Bool)
(declare-const c17 Err) ; get@1
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
(declare-const c18 SeqSeqBool) ; mem iface state
(assert (=> true (=> (= c17 nil) (and (not (= c11 0)) (not (= t15 0)) (not (select (SeqBool.at (select (SeqSeqBool.at c18) (select (SeqInt.at c13) (select (SeqInt.at (select (SeqSeqInt.at c14) c11)) (+ c12 64))))) (+ 2997695091990504928268101341469504234022244 0))) (<= 1 (select (SeqInt.at c13) (select (SeqInt.at (select (SeqSeqInt.at c14) c11)) (+ c12 64))))))))
(declare-datatype SeqSeqSeqInt ((SeqSeqSeqInt.mk (SeqSeqSeqInt.at (Array Int SeqSeqInt)) (SeqSeqSeqInt.raw Int))))
(define-fun SeqSeqSeqInt.len ((s SeqSeqSeqInt)) Int (ite (< (SeqSeqSeqInt.raw s) 0) 0 (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.store ((s SeqSeqSeqInt) (i Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) i v) (SeqSeqSeqInt.raw s)))
(define-fun SeqSeqSeqInt.fill ((n Int) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk ((as const (Array Int SeqSeqInt)) v) n))
(define-fun SeqSeqSeqInt.push ((s SeqSeqSeqInt) (v SeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (store (SeqSeqSeqInt.at s) (SeqSeqSeqInt.len s) v) (+ (SeqSeqSeqInt.len s) 1)))
(define-fun SeqSeqSeqInt.concat ((a SeqSeqSeqInt) (b SeqSeqSeqInt)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (ite (< j (SeqSeqSeqInt.len a)) (select (SeqSeqSeqInt.at a) j) (select (SeqSeqSeqInt.at b) (- j (SeqSeqSeqInt.len a))))) (+ (SeqSeqSeqInt.len a) (SeqSeqSeqInt.len b))))
(define-fun SeqSeqSeqInt.sub ((s SeqSeqSeqInt) (lo Int) (hi Int)) SeqSeqSeqInt (SeqSeqSeqInt.mk (lambda ((j Int)) (select (SeqSeqSeqInt.at s) (+ lo j))) (- hi lo)))
(declare-const c19 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Status
(define-fun t20 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c19) c11)) (+ c12 0)))
(declare-const c21 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.StatusCode
(define-fun t22 () Int (select (SeqInt.at (select (SeqSeqInt.at c21) c11)) (+ c12 16)))
(declare-const c23 SeqSeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Proto
(define-fun t24 () SeqInt (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c23) c11)) (+ c12 24)))
(declare-const c25 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMajor
(define-fun t26 () Int (select (SeqInt.at (select (SeqSeqInt.at c25) c11)) (+ c12 40)))
(declare-const c27 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ProtoMinor
(define-fun t28 () Int (select (SeqInt.at (select (SeqSeqInt.at c27) c11)) (+ c12 48)))
(declare-const c29 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Header
(define-fun t30 () Int (select (SeqInt.at (select (SeqSeqInt.at c29) c11)) (+ c12 56)))
(define-fun t31 () Int (select (SeqInt.at (select (SeqSeqInt.at c14) c11)) (+ c12 64)))
(define-fun t32 () Int (select (SeqInt.at c13) t31))
(declare-const c33 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.ContentLength
(define-fun t34 () Int (select (SeqInt.at (select (SeqSeqInt.at c33) c11)) (+ c12 80)))
(declare-const c35 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#ref
(define-fun t36 () Int (select (SeqInt.at (select (SeqSeqInt.at c35) c11)) (+ c12 88)))
(declare-const c37 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#off
(define-fun t38 () Int (select (SeqInt.at (select (SeqSeqInt.at c37) c11)) (+ c12 88)))
(declare-const c39 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#len
(define-fun t40 () Int (select (SeqInt.at (select (SeqSeqInt.at c39) c11)) (+ c12 88)))
(declare-const c41 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TransferEncoding#cap
(define-fun t42 () Int (select (SeqInt.at (select (SeqSeqInt.at c41) c11)) (+ c12 88)))
(declare-const c43 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Trailer
(define-fun t44 () Int (select (SeqInt.at (select (SeqSeqInt.at c43) c11)) (+ c12 120)))
(declare-const c45 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#ptr
(define-fun t46 () Int (select (SeqInt.at (select (SeqSeqInt.at c45) c11)) (+ c12 128)))
(declare-const c47 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.Request#at
(define-fun t48 () Int (select (SeqInt.at (select (SeqSeqInt.at c47) c11)) (+ c12 128)))
(declare-const c49 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#ptr
(define-fun t50 () Int (select (SeqInt.at (select (SeqSeqInt.at c49) c11)) (+ c12 136)))
(declare-const c51 SeqSeqInt) ; mem struct{Status string; StatusCode int; Proto string; ProtoMajor int; ProtoMinor int; Header net/http.Header; Body io.ReadCloser; ContentLength int64; TransferEncoding []string; Close bool; Uncompressed bool; Trailer net/http.Header; Request *net/http.Request; TLS *crypto/tls.ConnectionState}#0.TLS#at
(define-fun t52 () Int (select (SeqInt.at (select (SeqSeqInt.at c51) c11)) (+ c12 136)))
(declare-const c56 SeqSeqInt) ; mem map map[string][]string#1#val#ref
(declare-const c57 SeqSeqInt) ; mem map map[string][]string#1#val#off
(declare-const c58 SeqSeqInt) ; mem map map[string][]string#1#val#len
(declare-const c59 SeqSeqInt) ; mem map map[string][]string#1#val#cap
(declare-const c61 SeqSeqSeqInt) ; mem elem string#2
(assert (and (<= 0 c11) (< c11 c10) (<= 0 c12) (<= c12 281474976710656) (<= (SeqInt.len t20) 281474976710656) (<= (- 9223372036854775808) t22) (<= t22 9223372036854775807) (<= (SeqInt.len t24) 281474976710656) (<= (- 9223372036854775808) t26) (<= t26 9223372036854775807) (<= (- 9223372036854775808) t28) (<= t28 9223372036854775807) (<= 0 t30) (< t30 c10) (<= 0 t32) (< t32 c10) (< 0 (select (SeqInt.at c13) t31)) (<= (- 9223372036854775808) t34) (<= t34 9223372036854775807) (<= 0 t36) (< t36 c10) (<= 0 t38) (<= 0 t40) (<= t40 t42) (<= (+ (* t38 16) (* t42 16)) 281474976710656) (<= (- 9223372036854775808) t42) (<= t42 9223372036854775807) (<= 0 t44) (< t44 c10) (<= 0 t46) (< t46 c10) (<= 0 t48) (<= t48 281474976710656) (<= 0 t50) (< t50 c10) (<= 0 t52) (<= t52 281474976710656) (forall ((b53 Int)) (=> (and (<= 0 b53) (< b53 (SeqInt.len t20))) (and (<= 0 (select (SeqInt.at t20) b53)) (<= (select (SeqInt.at t20) b53) 255)))) (forall ((b54 Int)) (=> (and (<= 0 b54) (< b54 (SeqInt.len t24))) (and (<= 0 (select (SeqInt.at t24) b54)) (<= (select (SeqInt.at t24) b54) 255)))) (forall ((b55 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c56) t30)) b55)) (< (select (SeqInt.at (select (SeqSeqInt.at c56) t30)) b55) c10) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c57) t30)) b55)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c58) t30)) b55)) (<= (select (SeqInt.at (select (SeqSeqInt.at c58) t30)) b55) (select (SeqInt.at (select (SeqSeqInt.at c59) t30)) b55)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c57) t30)) b55) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c59) t30)) b55) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c59) t30)) b55)) (<= (select (SeqInt.at (select (SeqSeqInt.at c59) t30)) b55) 9223372036854775807))) (and (forall ((b60 Int)) (=> (and (<= 0 b60) (< b60 t40)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c61) t36)) (+ (+ t38 (* b60 1)) 0))) 281474976710656))) (forall ((b63 Int)) (! (=> (and (<= 0 (+ b63 (- (+ t38 0)))) (< (+ b63 (- (+ t38 0))) t40)) (<= (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c61) t36)) b63)) 281474976710656)) :pattern ((select (SeqSeqInt.at (select (SeqSeqSeqInt.at c61) t36)) b63))))) (forall ((b64 Int)) (=> (and (<= 0 b64) (< b64 t40)) (forall ((b65 Int)) (=> (and (<= 0 b65) (< b65 (SeqInt.len (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c61) t36)) (+ (+ t38 (* b64 1)) 0))))) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c61) t36)) (+ (+ t38 (* b64 1)) 0))) b65)) (<= (select (SeqInt.at (select (SeqSeqInt.at (select (SeqSeqSeqInt.at c61) t36)) (+ (+ t38 (* b64 1)) 0))) b65) 255)))))) (forall ((b66 Int)) (and (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c56) t44)) b66)) (< (select (SeqInt.at (select (SeqSeqInt.at c56) t44)) b66) c10) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c57) t44)) b66)) (<= 0 (select (SeqInt.at (select (SeqSeqInt.at c58) t44)) b66)) (<= (select (SeqInt.at (select (SeqSeqInt.at c58) t44)) b66) (select (SeqInt.at (select (SeqSeqInt.at c59) t44)) b66)) (<= (+ (* (select (SeqInt.at (select (SeqSeqInt.at c57) t44)) b66) 16) (* (select (SeqInt.at (select (SeqSeqInt.at c59) t44)) b66) 16)) 281474976710656) (<= (- 9223372036854775808) (select (SeqInt.at (select (SeqSeqInt.at c59) t44)) b66)) (<= (select (SeqInt.at (select (SeqSeqInt.at c59) t44)) b66) 9223372036854775807)))))
(assert true)
(assert (and t6 (forall ((b67 Int)) (=> (and (<= 0 b67) (< b67 (SeqInt.len t4))) (and (<= 0 c2) (<= c2 255))))))
(assert (and t8 (forall ((b68 Int)) (=> (and (<= 0 b68) (< b68 (SeqInt.len t4))) (and (<= 0 c2) (<= c2 255))))))
(declare-const c69 Err) ; some error 0
(assert (not (= c69 nil)))
(declare-const c70 Err) ; some error 1
(assert (not (= c70 nil)))
(assert (not (= c70 c69)))
(declare-const c71 Err) ; some error 2
(assert (not (= c71 nil)))
(assert (not (= c71 c69)))
(assert (not (= c71 c70)))
(declare-const c72 Err) ; some error 3
(assert (not (= c72 nil)))
(assert (not (= c72 c69)))
(assert (not (= c72 c70)))
(assert (not (= c72 c71)))
(declare-const c73 Err) ; some error 4
(assert (not (= c73 nil)))
(assert (not (= c73 c69)))
(assert (not (= c73 c70)))
(assert (not (= c73 c71)))
(assert (not (= c73 c72)))
(declare-const c74 Err) ; some error 5
(assert (not (= c74 nil)))
(assert (not (= c74 c69)))
(assert (not (= c74 c70)))
(assert (not (= c74 c71)))
(assert (not (= c74 c72)))
(assert (not (= c74 c73)))
(check-sat-using (then simplify propagate-values ctx-simplify simplify elim-uncnstr smt))

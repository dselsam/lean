(assert (= 1 (! 1 :ignore_this :ignore_this2 1 :ignore_this3 (1 2 3 (4 5)))))
(assert (= 1 1))
(check-sat)
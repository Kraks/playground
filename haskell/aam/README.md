Abstracting Abstract Machine
----

* `cek.hs` A concrete CEK machine

* `cesk.hs` A concrete CESK machine

* `cesk*.hs` A concrete CESK machine with store-allocated continuation

* `time-cesk*.hs` A concrete time-stamped CESK machine with store-allocated continuation

* `abs-time-cesk*.hs` An abstract time-stamped CESK machine with store-allocated continuation, but the address and time is unbound

* `k-cfa.hs` An abstract k-CFA-like machine, based on `abs-time-cesk*.hs`

* `0-cfa.hs` An abstract 0-CFA-like machine, simplied from `k-cfa.hs`

* `krivine.hs` A concrete call-by-need machine, aka Krivine's machine

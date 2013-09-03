pnerf
=====

* ./benchmarks/cprover_PN:
  * Files *.pl are input to the tool.
  * Conversion scripts are dk-to-pp-dk.sh and pp-dk-to-pl-petri-net.sh
  * Positive/negative results of the tool are in positive.list/negative.list.

* ./run-tests.sh:
  * Performs unit testing.
        
* ./tests/petersons-alg:
  * Unit tests corresponding to petri net for Peterson's
    Algorithm. Taken from Javier's notes on petri nets
    (http://www7.in.tum.de/um/courses/petri/SS2013/PNSkript.pdf,
    p. 16).
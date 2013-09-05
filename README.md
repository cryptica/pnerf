pnerf
=====

* ./benchmarks/
  * You obtain *.pl files by daisy chaining dk-to-pp-dk.sh and pp-dk-to-pl-petri-net.sh.

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

* TODO
  1. Running ./run_with_animation.sh myjob and then pressing C-c stops myjob.
  2. Let P be the properties of the terminal. Running
     ./run_with_animation.sh myjob and then pressing C-c restores P. - DONE
  3. Running ./run_with_animation.sh myjob prints the animation at the end of the output given by myjob. - Example 1 DONE 
  
     Example 1:
     
     $ ./run_with_animation.sh myjob
     second 01 - step1
     [ANIMATION]

     $ ./run_with_animation.sh myjob
     second 01 - step1
     second 03 - step2
     [ANIMATION]

     $ ./run_with_animation.sh myjob
     second 01 - step1
     second 03 - step2
     second 08 - step3
     [ANIMATION]

     ...and so on...

     Example 2:

     $ ./run_with_animation.sh 'myjob >/dev/null'
     [ANIMATION]

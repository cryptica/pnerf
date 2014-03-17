set terminal tikz latex size 12.5cm, 3.5cm
set output '../fig_performance_various.tex'

set datafile separator ','

set logscale
set xtics nomirror scale 1, 0 format "{\\tiny $10^{%T}$}"
set ytics nomirror scale 1, 0 format "{\\tiny $10^{%T}$}"
set ylabel offset 2, 0
unset key

set multiplot layout 1, 3

set xlabel "Safety over integers"
set ylabel "Ref. over integers"
plot x, \
    'cav2014-summary.csv' using \
    'T sfty-int':(column('I ref-int') != 0 ? column('T ref-int') : 1/0) \
    pt 7 ps 0.5 lt 3

set xlabel "Ref. w/o invariants"
set ylabel "Ref. w/ invariants"
plot x, \
    'cav2014-summary.csv' using \
    'T ref':(stringcolumn('R ref') eq '+' ? column('T inv-ref') : 1/0) \
    pt 7 ps 0.5 lt 3

set xlabel "Inv. w/o minimization"
set ylabel "Inv. w/ minimization"
plot x, \
    'cav2014-summary.csv' using \
    'T inv-ref':(stringcolumn('R inv-ref') eq '+' ? column('T inv-ref-min') : 1/0) \
    pt 7 ps 0.5 lt 3

unset multiplot

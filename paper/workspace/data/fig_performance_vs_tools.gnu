set terminal tikz latex size 12.5cm, 7cm
set output '../fig_performance_vs_tools.tex'

set datafile separator ','

set logscale
set xtics nomirror scale 1, 0 format "{\\tiny $10^{%T}$}"
set ytics nomirror scale 1, 0 format "{\\tiny $10^{%T}$}"
set ylabel offset 3, 0
unset key

set multiplot layout 2, 3

set xlabel "Ref. over integers"
set ylabel "IIC"
plot x, \
    'cav2014-summary.csv' using 'T ref-int':'T iic' \
    pt 7 ps 0.5 lt 3

set xlabel "Ref. over integers"
set ylabel "BFC"
plot x, \
    'cav2014-summary.csv' using 'T ref-int':'T bfc' \
    pt 7 ps 0.5 lt 3

set xlabel "Ref. over integers"
set ylabel "MIST2"
plot x, \
    'cav2014-summary.csv' using 'T ref-int':'T mist' \
    pt 7 ps 0.5 lt 3

set xlabel "Ref. w/ invariants"
set ylabel "IIC"
plot x, \
    'cav2014-summary.csv' using 'T inv-ref':'T iic' \
    pt 7 ps 0.5 lt 3

set xlabel "Ref. w/ invariants"
set ylabel "BFC"
plot x, \
    'cav2014-summary.csv' using 'T inv-ref':'T bfc' \
    pt 7 ps 0.5 lt 3

set xlabel "Ref. w/ invariants"
set ylabel "MIST2"
plot x, \
    'cav2014-summary.csv' using 'T inv-ref':'T mist' \
    pt 7 ps 0.5 lt 3

unset multiplot

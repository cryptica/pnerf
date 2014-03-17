set terminal tikz latex size 8cm, 3.5cm
set output '../fig_invariant_size.tex'

set datafile separator ','

set logscale
set xtics nomirror scale 1, 0 format "{\\tiny $10^{%T}$}"
set ytics nomirror scale 1, 0 format "{\\tiny $10^{%T}$}"
set ylabel offset 2, 0
unset key

set multiplot layout 1, 2

set xlabel "Number of places"
set ylabel "Size of invariant"
plot 'cav2014-summary.csv' using 'Plcs':'L inv-ref' pt 7 ps 0.5 lt 3

set xlabel "Petrinizer"
set ylabel "IIC"
plot x, \
    'cav2014-summary.csv' using 'L inv-ref':\
    (stringcolumn('R ref') eq '+' ? column('L iic') : 1/0) \
    pt 7 ps 0.5 lt 3

unset multiplot

# vim:syntax=gnuplot
#
#

set terminal png
set key left

set output "sort_cmp.png"
set title "Number of comparsions"
plot "sort.dat" index 0 using 1:2 t "Bubble sort" w lines,\
     "sort.dat" index 2 using 1:2 t "Shake sort" w lines,\
     "sort.dat" index 3 using 1:2 t "Quick sort" w lines,\
     "sort.dat" index 4 using 1:2 t "Heap sort" w lines

set output "sort_swap.png"
set title "Number of swaps"
plot "sort.dat" index 0 using 1:3 t "Bubble sort" w lines,\
     "sort.dat" index 2 using 1:3 t "Shake sort" w lines,\
     "sort.dat" index 3 using 1:3 t "Quick sort" w lines,\
     "sort.dat" index 4 using 1:3 t "Heap sort" w lines

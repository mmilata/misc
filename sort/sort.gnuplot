# vim:syntax=gnuplot
#
#

set terminal png
set key left

set output "sort_cmp.png"
set title "Number of comparsions"
load "cmp.inc"

set output "sort_swap.png"
set title "Number of swaps"
load "swap.inc"

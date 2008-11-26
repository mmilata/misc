#!/usr/bin/perl

for $p ('B'..'M') {
    print `cp robotA.svg robot$p.svg`;
    my $cmd = "perl -i -pe 's/A\\<\\/tspan/$p\\<\\/tspan/' robot$p.svg;";
#    print $cmd;
    print `$cmd`;
    print `convert robot$p.svg robot$p.png`;
}

for $p ('N'..'Y') {
    print `cp robotZ.svg robot$p.svg`;
    my $cmd = "perl -i -pe 's/Z\\<\\/tspan/$p\\<\\/tspan/' robot$p.svg;";
#    print $cmd;
    print `$cmd`;
    print `convert robot$p.svg robot$p.png`;
}

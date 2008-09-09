#!/usr/bin/perl

use warnings;
use strict;

use LWP;
use IO::Handle;
use DateTime;    # tohle se musi doinstalovat (cpan, apt...)
use Time::HiRes;

# usage:
#
# ve vypisu seminarnich skupin by mela url odkazu "zkusit se prihlasit" vypadat zhruba takto:
#
# https://is.muni.cz/auth/seminare/student.pl?fakulta=1433;obdobi=4384;studium=247554;predmet=454959;prihlasit=139597;akce=podrob;provest=1;stopwindow=1;design=m
#                                              $fakulta^    $obdobi^     $studium^      predmety^     sem.skupina^
#

# nasledujici promenne odpovidaji jednotlivym polozkam z url:
my $fakulta="1433";
my $obdobi="4384";
my $studium="247554";

# prihlasovaci udaje do ISu:
my $uco="256666";
my $heslo="mojetajne";

# adresar do ktereho se budou ukladat stranky pro pripadne pozdejsi prohlednuti
# pokud adresar neexistuje nebo do nej nejde zapisovat, soubory se neukladaji
my $save_dir="/home/elvis/tmp_seminator";

# seznam - predmet => sem.skupina
my %predmety = (
	"454959"	=> "139597", # ia006/05, sude ut. 10-12
	"454975"	=> "139658", # ib107/01, ut. 17-18
	"455001"	=> "139675", # mb000/04, po. 10-12
	"455037"	=> "139591", # pb154/09, suda st. 18-20

#	"454959"	=> "139599", # ia006/06, liche ut. 10-12
#	"455037"	=> "139589", # pb154/10, licha st. 18-20
);

# datum a cas, kdy zacina registrace
my $deadline_dt = DateTime->new(
	year	=> 2008,
	month	=> 9,
	day	=> 9,
	hour	=> 17,
	minute	=> 0,
#test#	hour => 21, minute => 33,
	second	=> 0,
	time_zone => "Europe/Prague"
);

# intervaly ve kterych se posilaji pozadavky
my @intervals = ( -2.0, -1.0, -0.5, -0.2, -0.1, -0.01, 0.0, 0.1, 0.2, 0.5, 1.0, 2.0 );

## pod timto radkem uz by nemelo byt nutne cokoli menit ##

my $deadline = [$deadline_dt->epoch(), 0];

STDOUT->autoflush(1);

my $ua = LWP::UserAgent->new;
$ua->agent("Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.9.0.1) Gecko/2008070206 Firefox/3.0.1");
$ua->credentials("is.muni.cz:443", "Information System MU", $uco => $heslo);

my $attempt = 1;
while(scalar @intervals){
	my $dif = Time::HiRes::tv_interval($deadline);
	if($dif > $intervals[0]){
		my $ival = $intervals[0];
		print "forking @ $ival\n";
		shift @intervals;

		foreach my $kod (keys %predmety){
			if(!fork){
				my $skupina = $predmety{$kod};
				print "$ival: $$: trying $kod - $skupina\n";

				my $url = "https://is.muni.cz/auth/seminare/student.pl?fakulta=$fakulta;obdobi=$obdobi;".
				          "studium=$studium;predmet=$kod;prihlasit=$skupina;akce=podrob;provest=1;stopwindow=1;design=m";
				my $req = HTTP::Request->new(GET => $url);
				my $res = $ua->request($req);
				if($res->is_success){
					my $content = $res->content;
					my %s = (
						"nelze se"	=> "nelze",
						"limit"		=> "vycerpan_limit",
						"jinam"		=> "prihlasen_jinam",
						"provedeno"	=> "uspech",
						"jste do vybra"	=> "zadna_zmena"
					);
					my $status = "unknown";

					foreach my $str (keys %s){
						if($content =~ /$str/){
							$status = $s{$str};
							last;
						}
					}

					print "$attempt: $kod: $skupina: $$: $status\n";
					if(open(FH, ">", "$save_dir/sem-$attempt-$kod-$skupina-$$-$status.html")){
						print FH $content;
						close FH;
					}
				}else{
					print "$attempt: $kod: $skupina: $$: error occured: ", $res->status_line, "\n";
				}
				exit;
			}
		}
		$attempt++;
	}else{
		Time::HiRes::usleep(6666);
	}
}

#!/usr/bin/perl

use warnings;
use strict;

use LWP;
use HTTP::Request::Common qw{ POST };
use IO::Handle;
use DateTime;    # tohle se musi doinstalovat (cpan, apt...)
use Time::HiRes;
use Term::ANSIColor qw(:constants);
use POSIX qw(WIFEXITED WEXITSTATUS);

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
my @orig_intervals = @intervals;

## pod timto radkem uz by nemelo byt nutne cokoli menit ##

use constant {
	RET_JESTENE	=> -1,
	RET_CHYBA	=> 2,
	RET_NELZE	=> 3,
	RET_LIMIT	=> 4,
	RET_JINAM	=> 5,
	RET_NIC 	=> 6,
	RET_USPECH	=> 7,
};

# 0 - pattern ktery se vyhledava v souboru
# 1 - nazev souboru do ktereho se uklada vystup
# 2 - navratovy kod
# 3 - max. petiznakovy retezec ktery bude v tabulce
# 4 - barva
# FIXME: barvicky rozbily %5s v printf, takze pokud ma status mene nez 5 znaku,
# vypada to blbe; jako workaround je treba to zatim rucne doplnit mezerama
my @retezce = (
	["nelze se",		"nelze",		RET_NELZE,	"nelze",	BLUE],
	["limit",		"vycerpan_limit",	RET_LIMIT,	"limit",	RED],
	["jinam",		"prihlasen_jinam",	RET_JINAM,	"jinam",	BLUE],
	["provedeno",		"uspech",		RET_USPECH,	"   OK",	GREEN],
	["jste do vybra",	"zadna_zmena",		RET_NIC,	"  nic",	GREEN],
	[undef,			"chyba",		RET_CHYBA,	"chyba",	RED],
	[undef,			undef,			RET_JESTENE,	"cekam",	BLUE],
);

my $deadline = [$deadline_dt->epoch(), 0];
my %pids;   # pid forknutych procesu (indexovano podle predmetu a intervalu)
my %states; # navratove hodnoty (indexovano podle pid)

STDOUT->autoflush(1);

my $ua = LWP::UserAgent->new;
$ua->agent("Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.9.0.1) Gecko/2008070206 Firefox/3.0.1");
$ua->cookie_jar({});

# login
my $login_url = 'https://is.muni.cz/system/login_form.pl';
#my $login_url = 'http://localhost:12345/';
my $req = POST ($login_url, [
	destination => '/auth/',
	'credential_0' => $uco,
	'credential_1' => $heslo,
	'credential_2' => '28800',
	submit => 'Přihlásit se' ]);
my $res = $ua->request($req);
if($res->is_success){
	print 'login successful'
}else{
	print "error occured: ", $res->status_line, "\n";
}

my $attempt = 1;
my $forked = 0;
while(scalar @intervals){
	my $dif = Time::HiRes::tv_interval($deadline);
	if($dif > $intervals[0]){
		my $ival = shift @intervals;
		print "Time: $ival, sending requests\n";

		foreach my $kod (keys %predmety){
			my $skupina = $predmety{$kod};
			my $pid = fork;

			if(!defined $pid){
				print "$ival: forking $kod - $skupina failed\n";
			}elsif($pid==0){
				ZkusRegistraci($kod,$skupina,$ival,$attempt);
			}else{
				$pids{$kod}->{$ival} = $pid;
				$states{$pid} = RET_JESTENE;
				$forked++;
			}
		}
		$attempt++;
	}else{
		Time::HiRes::usleep(6666);
	}
}

PrekresliStatus();
while($forked){
	my $pid = wait;
	if(WIFEXITED($?)) {
		$states{$pid} = WEXITSTATUS($?);
		PrekresliStatus();
	}else{
		print "error: child $pid exited abnormally\n";
	}
	$forked--;
}

exit 0;

## definice funkci ##

sub ZkusRegistraci
{
	my ($kod,$skupina,$ival) = @_;

	#print "$ival: $$: trying $kod - $skupina\n";

	my $url = "https://is.muni.cz/auth/seminare/student.pl?fakulta=$fakulta;obdobi=$obdobi;".
		  "studium=$studium;predmet=$kod;prihlasit=$skupina;akce=podrob;provest=1;stopwindow=1;design=m";
	my $req = HTTP::Request->new(GET => $url);
	my $res = $ua->request($req);

	if($res->is_success){
		my $content = $res->content;
		my $file_status = "unknown";
		my $return_status = 1;

		foreach my $line (@retezce){
			my $pattern = $line->[0];
			next unless (defined $pattern);

			if($content =~ /$line->[0]/){
				$file_status = $line->[1];
				$return_status = $line->[2];
				last;
			}
		}

		#print "$attempt: $kod: $skupina: $$: $file_status\n";
		if(open(FH, ">", "$save_dir/sem-$attempt-$kod-$skupina-$$-$file_status.html")){
			print FH $content;
			close FH;
		}
		exit $return_status;
	}else{
		#print "$attempt: $kod: $skupina: $$: error occured: ", $res->status_line, "\n";
		exit RET_CHYBA;
	}
}

sub PrekresliStatus
{
	#print "\033[2J"; # clear the screen, the ugly way
	print "         ";
	foreach my $ival (@orig_intervals) {
		printf("%5s ",$ival);
	}
	print "\n";

	foreach my $predmet (keys %predmety) {
		printf("%8s ",$predmet);
		foreach my $ival (@orig_intervals) {
			my $pid = $pids{$predmet}->{$ival};
			my $retcode = $states{$pid};
			printf("%5s ",TxtStatus($retcode));
		}
		print "\n";
	}
	print "\n";
}

sub TxtStatus
{
	my ($retcode) = @_;
	my $res = "";

	foreach my $line (@retezce) {
		if ($line->[2] == $retcode) {
			$res .= $line->[4];
			$res .= $line->[3];
			$res .= CLEAR;
			return $res;
		}
	}

	return (RED."chyb2".CLEAR);
}

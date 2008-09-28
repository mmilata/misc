use Irssi;
use Mail::Sendmail; # perl -MCPAN -e "install Mail::Sendmail"
use vars qw($VERSION %IRSSI $block); 

$VERSION = "0.1";
%IRSSI = (
	authors         => "b42",
	contact         => "b42\@srck.net",
	name            => "hilight_mailer",
	description     => "Sends messages matching regexp to email",
	license         => "WTFPL"
);

$block = 0;

sub sig_privmsg {
  my ($server, $data, $nick, $address) = @_;
  my ($target, $text) = split(/ :/, $data, 2);
  my $timeout_secs = Irssi::settings_get_int('hilight_mailer_block_secs');

  # do nothing if we're not away
  return if(Irssi::settings_get_bool('hilight_mailer_awayonly')
            && not $server->{usermode_away});

  # do nothing if we did something recently
  return if $block;

  my @regexes = split(/\s*,\s*/, Irssi::settings_get_str('hilight_mailer_regexes'));

  foreach $re (@regexes) {
    if($text =~ /$re/){

      # send the message
      my %mail = (
        From    => Irssi::settings_get_str('hilight_mailer_from'),
        To      => Irssi::settings_get_str('hilight_mailer_email'),
        Subject => "irssi: $re",
        Body    => "hilight $re in $target: <$nick> $text",
        Smtp    => Irssi::settings_get_str('hilight_mailer_smtp')
      );
      sendmail(%mail) or Irssi::print("hilight_mailer: failed to send message");

      # set timeout if not 0
      if($timeout_secs){
        Irssi::timeout_add_once(1000 * $timeout_secs, 'timeout', 0);
        $block = 1;
      }
      last;
    }
  }
}

sub timeout {
  $block = 0;
}

Irssi::signal_add('event privmsg', 'sig_privmsg');
Irssi::settings_add_str('misc', 'hilight_mailer_regexes', 'beer');
Irssi::settings_add_str('misc', 'hilight_mailer_email', 'root@localhost');
Irssi::settings_add_str('misc', 'hilight_mailer_from', 'irssi@localhost');
Irssi::settings_add_str('misc', 'hilight_mailer_smtp', 'localhost');
Irssi::settings_add_bool('misc', 'hilight_mailer_awayonly', 1);
Irssi::settings_add_int('misc', 'hilight_mailer_block_secs', 60);

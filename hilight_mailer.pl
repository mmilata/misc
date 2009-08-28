use Irssi;
use Mail::Sendmail; # perl -MCPAN -e "install Mail::Sendmail"
use vars qw($VERSION %IRSSI $block); 

$VERSION = "0.2";
%IRSSI = (
	authors         => "b42",
	contact         => "b42\@srck.net",
	name            => "hilight_mailer",
	description     => "Sends messages matching regexp to email",
	license         => "WTFPL"
);
# parts stolen from Prema's script

$block = 0;

sub sig_printtext {
  my ($dest, $text, $stripped) = @_;
  my $timeout_secs = Irssi::settings_get_int('hilight_mailer_block_secs');
  $target = $dest->{target};
  $server = $dest->{server};

  # do nothing if we're not away
  return if(Irssi::settings_get_bool('hilight_mailer_awayonly')
            && not $server->{usermode_away});

  # do nothing if we're not hilighted
  return unless
    $dest->{level} & (MSGLEVEL_HILIGHT|MSGLEVEL_MSGS);
  return if
    $dest->{level} & MSGLEVEL_NOHILIGHT;

  # do nothing if we did something recently
  if($block){
    Irssi::print "hilight_mailer: temporarily blocked, not sending anything";
    return;
  }

  # send the message
  my %mail = (
    From    => Irssi::settings_get_str('hilight_mailer_from'),
    To      => Irssi::settings_get_str('hilight_mailer_email'),
    Subject => "irssi hilight",
    Body    => "$target: $stripped",
    Smtp    => Irssi::settings_get_str('hilight_mailer_smtp')
  );
  sendmail(%mail) or Irssi::print("hilight_mailer: failed to send message");

  # set timeout if not 0
  if($timeout_secs){
    Irssi::timeout_add_once(1000 * $timeout_secs, 'timeout', 0);
    $block = 1;
  }
}

sub timeout {
  $block = 0;
}

Irssi::signal_add('print text', \&sig_printtext);
Irssi::settings_add_str('misc', 'hilight_mailer_email', 'root@localhost');
Irssi::settings_add_str('misc', 'hilight_mailer_from', 'irssi@localhost');
Irssi::settings_add_str('misc', 'hilight_mailer_smtp', 'localhost');
Irssi::settings_add_bool('misc', 'hilight_mailer_awayonly', 1);
Irssi::settings_add_int('misc', 'hilight_mailer_block_secs', 60);

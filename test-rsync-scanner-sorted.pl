#!/usr/bin/perl -w

use strict;

use DBI;
use Date::Parse;
use LWP::UserAgent;
use Net::FTP;
use Net::Domain;
use Data::Dumper;
use Time::HiRes;
use Socket;
use bytes;
use Config::IniFiles;
use Time::HiRes qw(gettimeofday);
use Encode;

my $version = '2.19.0';
my $verbose = 3;
my $sqlverbose = 0;

#$DB::inhibit_exit = 0;

$SIG{'PIPE'} = 'IGNORE';

$SIG{__DIE__} = sub {
  my @a = ((caller 3)[1..3], '=>', (caller 2)[1..3], '=>', (caller 1)[1..3]);
  print "__DIE__: (@a)\n";
  die @_;
};

$SIG{USR1} = sub { $verbose++; warn "sigusr1 seen. ++verbose = $verbose\n"; };
$SIG{USR2} = sub { $verbose--; warn "sigusr2 seen. --verbose = $verbose\n"; };

$ENV{FTP_PASSIVE} = 1;	# used in LWP only, Net::FTP ignores this.


# Create a user agent object
my $ua = LWP::UserAgent->new;
$ua->agent("MirrorBrain Scanner/$version (See http://mirrorbrain.org/scanner_info)");

my $rsync_muxbuf = '';
my $all_servers = 0;
my $start_dir = '/';
my $parallel = 1;
my $list_only = 0;
my $recursion_delay = 0;	# seconds delay per *_readdir recuursion
my $force_scan = 0;
my $enable_after_scan = 0;
my $cfgfile = '/etc/mirrorbrain.conf';
my $brain_instance = '';

# save prepared statements
my $sth_update;
my $sth_insert_rel;
my $sth_select_file;
my $sth_insert_file;
my $sth_mirr_addbypath;

my $gig2 = 1<<31; # 2*1024*1024*1024 == 2^1 * 2^10 * 2^10 * 2^10 = 2^31

# these two vars are used in the largefile_check's http request callback to end
# transmission after a maximum amount of data (specified by $http_slice_counter)
my $http_size_hint;
my $http_slice_counter;

# directories to be included from top-level
my @top_include_list;

my @exclude_list;
my @exclude_list_rsync;
# default excludes:
push @exclude_list, '/.~tmp~/';
push @exclude_list_rsync, '*/.~tmp~/';
push @exclude_list_rsync, '/.~tmp~/';

my $ftp_timer_global;

# exit usage() unless @ARGV;
while (defined (my $arg = shift)) {
	if    ($arg !~ m{^-})                  { unshift @ARGV, $arg; last; }
	elsif ($arg =~ m{^(-h|--help|-\?)})    { exit usage(); }
	elsif ($arg =~ m{^(-I|--top-include)}) { push @top_include_list, shift; }
	elsif ($arg =~ m{^--exclude$})         { push @exclude_list, shift; }
	elsif ($arg =~ m{^--exclude-rsync$})   { push @exclude_list_rsync, shift; }
	elsif ($arg =~ m{^-q})                 { $verbose--; }
	elsif ($arg =~ m{^-v})                 { $verbose++; }
	elsif ($arg =~ m{^-S})                 { $sqlverbose++; }
	elsif ($arg =~ m{^-a})                 { $all_servers++; }
	elsif ($arg =~ m{^-j})                 { $parallel = shift; }
	elsif ($arg =~ m{^-e})                 { $enable_after_scan++; }
	elsif ($arg =~ m{^-f})                 { $force_scan++; }
	elsif ($arg =~ m{^-d})                 { $start_dir = shift; }
	elsif ($arg =~ m{^--config})           { $cfgfile = shift; }
	elsif ($arg =~ m{^-b})                 { $brain_instance = shift; }
	elsif ($arg =~ m{^-l})                 { $list_only++; 
						 $list_only++ if $arg =~ m{ll}; 
						 $list_only++ if $arg =~ m{lll}; }
	elsif ($arg =~ m{^-})		       { exit usage("unknown option '$arg'"); }
}

# my @scan_list = ("rsync://opensuse.mirror.liquidtelecom.com/opensuse-full/repositories"); 
# my @scan_list = ("rsync://mirror.karneval.cz/opensuse/repositories"); 
my @scan_list = ("rsync://ftp.gwdg.de/pub/opensuse/repositories/network:"); 

for my $row (@scan_list) {
  print localtime(time) . " $row: starting\n" if $verbose > 0;

  my $start = int(gettimeofday * 1000);
  my $file_count = rsync_readdir(1, 1, $row, $start_dir);

  my $duration = (int(gettimeofday * 1000) - $start) / 1000;
  if (!$duration) { $duration = 1; }
  if (!$file_count) { $file_count = 0; }

  my $fpm = int(60*$file_count/$duration);

  print localtime(time) . " $row: scanned $file_count files (" 
         . int($fpm/60) . "/s) in " 
         . int($duration) . "s\n" if $verbose > 0;

  print localtime(time) . " $row: done.\n" if $verbose > 0;
}

exit 0;
###################################################################################################

sub usage
{
  my ($msg) = @_;

  print STDERR qq{$0 V$version usage:

scanner [options] [mirror_ids ...]

  -b        MirrorBrain instance to use 
            Default: the first which is defined in the config.
  -v        Be more verbose (Default: $verbose).
  -S        Show SQL statements.
  -q        Be quiet.
  -l        Do not scan. List enabled mirrors only.
  -ll       As -l, but include disabled mirrors and print urls.
  -lll      As -ll, but all in one grep-friendly line.

  -a        Scan all enabled mirrors. Alternative to providing a list of mirror_ids.
  -e        Enable mirror, after it was scanned. Useful with -f.
  -f        Force. Scan listed mirror_ids even if they are not enabled.
  -d dir    Scan only in dir under mirror's baseurl. 
            Default: start at baseurl.

  -j N      Run up to N scanner queries in parallel.

  --exclude regexp 
            Define pattern(s) for path names to ignore. Paths matching this pattern
            will not be recursed into (thus saving resources) and also, when
            matching a file, not added into the database.
            This option is effective only for scans via HTTP/FTP. For rsync,
            use the --exclude-rsync option (due to different patterns used there).
            Here, regular expressions are used. 
            Path names don't start with a slash; thus, if the regexp starts with a slash
            it will not match at the top-level directory.
            Option can be repeated.
            Default: @exclude_list
  --exclude-rsync pattern 
            Similar like --exclude, but used (only) for rsync scans.
            For HTTP/FTP, use the --exclude option (due to different patterns
            used there).
            The patterns are rsync(1) patterns. Option can be repeated.
            Default: @exclude_list_rsync

  -T dir    Directory to be scanned at the top level; option can be repeated.

Both, names(identifier) and numbers(id) are accepted as mirror_ids.
};
  print STDERR "\nERROR: $msg\n" if $msg;
  return 0;
}

sub byte_size
{
  my ($len) = @_;
  return $len unless $len =~ m{(.*)([KMG])$};
  my ($n, $l) = ($1,$2);
  return int($n*1024)           if $l eq 'K';
  return int($1*1024*1024)      if $l eq 'M';
  return int($1*1024*1024*1024) if $l eq 'G';
  die "byte_size: $len not impl\n";
}

sub save_file
{
  my ($path, $identifier, $serverid, $mod_re, $ign_re, $save) = @_;
  $path =~ s{^/+}{};  # be sure we have no leading slashes.
  $path =~ s{//+}{/}g;  # avoid double slashes.

  # explicitely tell Perl that the filename is in UTF-8 encoding
  $path = decode_utf8($path);

  return $path;
}


# callback function
sub rsync_cb
{
  my ($priv, $name, $len, $mode, $mtime) = @_;
  return 0 if $name eq '.' or $name eq '..';
  my $r = 0;

  if($priv->{subdir}) {
    # subdir is expected not to start or end in slashes.
    $name = $priv->{subdir} . '/' . $name;
  }

  if($mode & 0x1000) {        # directories have 0 here.
    if($mode & 004) { # readable for the world is good.
      # params for largefile check: url=$ary_ref->{$priv->{serverid}}/$name, size=$len
      if(largefile_check($priv->{identifier}, $priv->{serverid}, $name, $len) == 0) {
        printf "$priv->{identifier}: warning: $name cannot be delivered via HTTP! Skipping\n" if $verbose > 0;
      }
      else {
        $name = save_file($name, $priv->{identifier}, $priv->{serverid}, $mtime, $priv->{re});
        $priv->{counter}++;
        $r = [$name, $len, $mode, $mtime];
        printf "%03o %12.0f %-25s %-50s\n", ($mode & 0777), $len, scalar(localtime $mtime), $name if $verbose > 2;
      }
    }
    else {
      printf "%03o %12.0f %-25s %-50s\n", ($mode & 0777), $len, scalar(localtime $mtime), $name if $verbose > 1;
    }
  }
  elsif($mode == 0755) {
    printf "%03o %12.0f %-25s %-50s\n", ($mode & 0777), $len, scalar(localtime $mtime), $name if $verbose > 1;
  }
  elsif($mode == 020777) {
    printf "%03o %12.0f %-25s %-50s\n", ($mode & 0777), $len, scalar(localtime $mtime), $name if $verbose > 2;
  }
  return $r;
}



# example rsync address:
#  rsync://user:passwd@ftp.sunet.se/pub/Linux/distributions/opensuse/#@^opensuse/@@
# parameters:
#  serverid: id field content from database row
#  url: base url from database
#  d: base directory (can be 'undef'): parameter to the '-d' switch
sub rsync_readdir
{
  my ($identifier, $serverid, $url, $d) = @_;
  return 0 unless $url;

  $url =~ s{^rsync://}{}s; # trailing s: treat as single line, strip off protocol id
  my $re = ''; $re = $1 if $url =~ s{#(.*?)$}{}; # after a hash can be a regexp, see example above
  my $cred = $1 if $url =~ s{^(.*?)@}{}; # username/passwd if specified
  die "$identifier: rsync_readdir: cannot parse url '$url'\n" unless $url =~ m{^([^:/]+)(:(\d*))?(.*)$};
  my ($host, $dummy, $port, $path) = ($1,$2,$3,$4);
  $port = 873 unless $port;
  $path =~ s{^/+}{};

  my $peer = { identifier => $identifier, addr => inet_aton($host), port => $port, serverid => $serverid };
  $peer->{re} = $re if $re;
  $peer->{pass} = $1 if $cred and $cred =~ s{:(.*)}{};
  $peer->{user} = $cred if $cred;
  $peer->{subdir} = $d if length $d;
  $peer->{counter} = 0;
  $path .= "/". $d if length $d;
  rsync_get_filelist($identifier, $peer, $path, 0, \&rsync_cb, $peer, 1);
  return $peer->{counter};
}


#######################################################################
# rsync protocol
#######################################################################
#
# Copyright (c) 2005 Michael Schroeder (mls@suse.de)
#
# This program is licensed under the BSD license, read LICENSE.BSD
# for further information
#
sub sread
{
  local *SS = shift;
  my $len = shift;
  my $ret = '';
  while($len > 0) {
    alarm 600;
    my $r = sysread(SS, $ret, $len, length($ret));
    alarm 0;
    die("read error") unless $r;
    $len -= $r;
    die("read too much") if $r < 0;
  }
  return $ret;
}



sub swrite
{
  local *SS = shift;
  my ($var, $len) = @_;
  $len = length($var) unless defined $len;
  return if $len == (syswrite(SS, $var, $len) || 0); 
  warn "syswrite: $!\n";
}



sub muxread
{
  my $identifier = shift;
  local *SS = shift;
  my $len = shift;

  #print "$identifier: muxread $len\n";
  while(length($rsync_muxbuf) < $len) {
    #print "$identifier: muxbuf len now ".length($muxbuf)."\n";
    my $tag = '';
    $tag = sread(*SS, 4);
    $tag = unpack('V', $tag);
    my $tlen = 0+$tag & 0xffffff;
    $tag >>= 24;
    if ($tag == 7) {
      $rsync_muxbuf .= sread(*SS, $tlen);
      next;
    }
    if ($tag == 8 || $tag == 9) {
      my $msg = sread(*SS, $tlen);
      warn("$identifier: tag=8 $msg\n") if $tag == 8;
      print "$identifier: info: $msg\n";
      next;
    }
    warn("$identifier: unknown tag: $tag\n");
    return undef;
  }
  my $ret = substr($rsync_muxbuf, 0, $len);
  $rsync_muxbuf = substr($rsync_muxbuf, $len);
  return $ret;
}



sub rsync_get_filelist
{
  my ($identifier, $peer, $syncroot, $norecurse, $callback, $priv, $sorted) = @_;
  my $syncaddr = $peer->{addr};
  my $syncport = $peer->{port};

  $SIG{ALRM} = sub { $verbose++; $verbose++; die localtime(time) . " $identifier: rsync timeout...\n" };

  if(!defined($peer->{have_md4})) {
    ## why not rely on %INC here?
    $peer->{have_md4} = 0;
    eval {
      # this causes funny messages, if perl-Digest-MD4 is not installed:
      # __DIE__: (/usr/bin/scanner 311 main::rsync_readdir => /usr/bin/scanner 961 main::rsync_get_filelist => /usr/bin/scanner 1046 (eval)) 
      # not sure whether it is worth installing it.
      # we never had it on mirrordb.opensuse.org, the main openSUSE scan host.
      require Digest::MD4;
      $peer->{have_md4} = 1;
    };
  }
  $syncroot =~ s/^\/+//;
  my $module = $syncroot;
  $module =~ s/\/.*//;
  my $tcpproto = getprotobyname('tcp');
  socket(S, PF_INET, SOCK_STREAM, $tcpproto) || die("$identifier: socket: $!\n");
  setsockopt(S, SOL_SOCKET, SO_KEEPALIVE, pack("l",1));
  connect(S, sockaddr_in($syncport, $syncaddr)) || die("$identifier: connect: $!\n");
  my $hello = "\@RSYNCD: 28\n";
  swrite(*S, $hello);
  my $buf = '';
  alarm 600;
  sysread(S, $buf, 4096);
  alarm 0;
  die("$identifier: protocol error [$buf]\n") if $buf !~ /^\@RSYNCD: ([\d.]+)\n/s;
  $peer->{rsync_protocol} = $1;
  $peer->{rsync_protocol} = 28 if $peer->{rsync_protocol} > 28;
  swrite(*S, "$module\n");
  while(1) {
    alarm 600;
    sysread(S, $buf, 4096);
    alarm 0;
    die("$identifier: protocol error [$buf]\n") if $buf !~ s/\n//s;
    last if $buf eq "\@RSYNCD: OK";
    die("$identifier: $buf\n") if $buf =~ /^\@ERROR/s;
    if($buf =~ /^\@RSYNCD: AUTHREQD /) {
      die("$identifier: '$module' needs authentification, but Digest::MD4 is not installed\n") unless $peer->{have_md4};
      my ($user,$password)='';
      # my $user = "nobody"; is not needed IMO
      $user = $peer->{user} if defined $peer->{user};
      $password = $peer->{pass} if defined $peer->{pass};
      my $digest = "$user ".Digest::MD4::md4_base64("\0\0\0\0$password".substr($buf, 18))."\n";
      swrite(*S, $digest);
      next;
    }
  }
  my @args = ('--server', '--sender', '-rl');
  push @args, '--exclude=/*/*' if $norecurse;

  if(@top_include_list && !defined($peer->{subdir})) {
    foreach my $item (@top_include_list) {
      push @args, "--include=/$item";
    }
    push @args, "--exclude=/*";
  }

  print "$identifier: rsync excludes: @exclude_list_rsync\n" if $verbose > 1;
  foreach my $item (@exclude_list_rsync) {
    push @args, "--exclude=$item";
  }
  print "$identifier: rsync args: @args\n" if $verbose > 2;

  for my $arg (@args, '.', "$syncroot/.", '') {
    swrite(*S, "$arg\n");
  }
  sread(*S, 4);	# checksum seed
  swrite(*S, "\0\0\0\0");
  my @filelist;
  my $name = '';
  my $mtime = 0;
  my $mode = 0;
  my $uid = 0;
  my $gid = 0;
  my $flags;
  while(1) {
    $flags = muxread($identifier, *S, 1);
    $flags = ord($flags);
    # printf "flags = %02x\n", $flags;
    last if $flags == 0;
    $flags |= ord(muxread($identifier, *S, 1)) << 8 if $peer->{rsync_protocol} >= 28 && ($flags & 0x04) != 0;
    my $l1 = $flags & 0x20 ? ord(muxread($identifier, *S, 1)) : 0;
    my $l2 = $flags & 0x40 ? unpack('V', muxread($identifier, *S, 4)) : ord(muxread($identifier, *S, 1));
    $name = substr($name, 0, $l1).muxread($identifier, *S, $l2);
    my $len = unpack('V', muxread($identifier, *S, 4));
    if($len == 0xffffffff) {
      $len = unpack('V', muxread($identifier, *S, 4));
      my $len2 = unpack('V', muxread($identifier, *S, 4));
      $len += $len2 * 4294967296;
    }
    $mtime = unpack('V', muxread($identifier, *S, 4)) unless $flags & 0x80;
    $mode = unpack('V', muxread($identifier, *S, 4)) unless $flags & 0x02;
    my $mmode = $mode & 07777;
    if(($mode & 0170000) == 0100000) {
      $mmode |= 0x1000;
    } elsif (($mode & 0170000) == 0040000) {
      $mmode |= 0x0000;
    } elsif (($mode & 0170000) == 0120000) {
      $mmode |= 0x2000;
      muxread($identifier, *S, unpack('V', muxread($identifier, *S, 4)));
    } else {
      print "$name: unknown mode: $mode\n";
      next;
    }
    # print "$name :: $mmode\n";
    # sort and process buffer when folder changes
    if ($callback && $sorted && !($mmode & 0x1000)) {
        # print "FOLDER!!\n";
        for my $file (sort {$a->[0] cmp $b->[0]} @filelist) {
            &$callback($priv, $file->[0], $file->[1], $file->[2], $file->[3], $file->[4]);
        }
        @filelist = ();
    }
    if(!$sorted && $callback) {
      &$callback($priv, $name, $len, $mmode, $mtime);
    }
    else {
      push @filelist, [$name, $len, $mmode, $mtime];
    }
  }
  my $io_error = unpack('V', muxread($identifier, *S, 4));

  # rsync_send_fin
  swrite(*S, pack('V', -1));      # switch to phase 2
  swrite(*S, pack('V', -1));      # switch to phase 3
  if($peer->{rsync_protocol} >= 24) {
    swrite(*S, pack('V', -1));    # goodbye
  }
  close(S);
  if ($callback && $sorted) {
    # sort and process remaining buffer
    for my $file (sort {$a->[0] cmp $b->[0]} @filelist) {
      &$callback($priv, $file->[0], $file->[1], $file->[2], $file->[3]);
    }
  }
  return undef if $callback;
  return @filelist unless $sorted;
  return sort {$a->[0] cmp $b->[0]} @filelist;
}

# double check large files.
# some mirrors can't deliver large files via http.
# try a http range request for files larger than 2G/4G in http/ftp/rsync
sub largefile_check
{
  my ($identifier, $id, $path, $size, $recurse) = @_;
    return 1;

  if(not defined $recurse) {
    $recurse = 0;
  }
  # don't follow more than three redirections
  return if($recurse >= 3);

  $http_size_hint = 128;
  $http_slice_counter = 2*$http_size_hint;

  if($size==0) {
    if($path =~ m{.*\.iso$}) {
      print "$identifier: Error: cd size is zero! Illegal file $path\n";
      goto error;
    }
  }

  goto all_ok if($size <= $gig2);

  my $aa = <<'END_MESSAGE';
my $url = "$ary_ref->{$id}->{baseurl}/$path";
  my $header = new HTTP::Headers('Range' => "bytes=".($gig2-$http_size_hint)."-".($gig2+1));
  my $req = new HTTP::Request('GET', "$url", $header);

  #turn off implicit redirects (handle manually):
  $ua->max_redirect(0);

  my $result = $ua->request(
    $req,
    sub {
      my ($chunk, $result) = @_;
      $http_slice_counter -= $http_size_hint;
      die() if $http_slice_counter <= 0;
      return $chunk;
    },
    $http_size_hint
  );

  my $code = $result->code();
  goto all_ok if($code == 206 or $code == 200);
  # check some redirect types:
  # 301 - permanent redirect -> client is adviesd to remember redirected address
  # 302 - temporary redirect -> client shall continue using this address
  # 303 - redirect from POST command to another URI via GET command
  # 307 - same as 302 except different caching behaviour
  if($code == 301 or $code == 302 or $code == 303 or $code == 307) {
    if($result->header('location') =~ m{^ftp:.*}) {
      print localtime(time) . " $identifier: Moved to ftp location, assuming success if followed\n" if $verbose >= 1;
      goto all_ok;
    }
    if($result->header('location') =~ m{^http:.*}) {
      print localtime(time) . " $identifier: [RECURSE] Moved to other http location, recursing scan...\n" if $verbose >= 1;
      return largefile_check($id, $result->header('location'), $size, $recurse+1);
    }
  }

  if($result->code() == 416) {
    print localtime(time) . " $identifier: Error: range error: filesize broken for file $url\n" if $verbose >= 1;
  }
  else {
    print localtime(time) . " $identifier: Error ".$result->code()." occured\n" if $verbose >= 1;
  };
END_MESSAGE

  error:
  return 0;

  all_ok:
  return 1;
}

# vim: ai ts=2 sw=2 smarttab expandtab

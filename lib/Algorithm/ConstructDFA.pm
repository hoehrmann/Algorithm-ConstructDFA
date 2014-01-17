package Algorithm::ConstructDFA;

use 5.012000;
use strict;
use warnings;
use base qw(Exporter);
use Storable qw/freeze thaw/;
use List::UtilsBy qw/partition_by/;
use List::MoreUtils qw/uniq/;
use Data::AutoBimap;
use Memoize;

our $VERSION = '0.01';

our %EXPORT_TAGS = ( 'all' => [ qw(
	construct_dfa
) ] );

our @EXPORT_OK = ( @{ $EXPORT_TAGS{'all'} } );

our @EXPORT = qw(
  construct_dfa
);

local $Storable::canonical = 1;

sub _get_graph {
  my ($root, $labelf, $nullablef, $successorsf, $acceptingf) = @_;

  my $m = Data::AutoBimap->new();
  
  my $label = memoize(sub { $labelf->($m->n2s($_[0])) });

  my $successors = memoize(sub {
    map { $m->s2n($_) } $successorsf->($m->n2s($_[0]))
  });

  my $accepting = memoize(sub {
    !!$acceptingf->(map { $m->n2s($_) } @_)
  });
  
  my $nullable = memoize(sub {
    !!$nullablef->($m->n2s($_[0]))
  });

  my $all_reachable_and_self = sub {
    my ($v) = @_;
    my %seen;
    my @todo = ($v);
    while (@todo) {
      my $c = pop @todo;
      next if $seen{$c}++;
      push @todo, $successors->($v) if $nullable->($c);
    }
    keys %seen;
  };
  
  my $root_id = $m->s2n($root);
  my $start = [ $root_id ];

  $start = [sort { $a cmp $b } uniq
    $all_reachable_and_self->($root_id)]
      if $nullable->($root_id);
      
  my $start_s = join ' ', @$start;
    
  my @todo = ($start);
  my %seen;
  my $dfa;

  my @accepting_dfa_states;
  my %predecessors;
  
  while (@todo) {
    my $src = pop @todo;
    my @src = @{ $src };
    my $src_s = join ' ', @src;
    next if $seen{$src_s}++;
    
    my $src_accepts = $accepting->(@src);
    push @accepting_dfa_states, $src_s if $src_accepts;
    
    my %p = partition_by { $label->($_) } @src;
    
    while (my ($k, $v) = each %p) {
      my @dst = sort { $a cmp $b } uniq map {
        $all_reachable_and_self->($_)
      } map {
        $successors->($_)
      } @$v;

      push @todo, \@dst;
      my $dst_s = join ' ', @dst;
      $dfa->{$src_s}->{$k} = $dst_s;
      $predecessors{$dst_s}->{$src_s}++;
    }
  }
  
  my %reachable = do {
    my %seen;
    my @todo = @accepting_dfa_states;
    while (@todo) {
      my $c = pop @todo;
      next if $seen{$c}++;
      push @todo, keys %{ $predecessors{$c} };
    }
    map { $_ => 1 } keys %seen;
  };
  
  my $o = Data::AutoBimap->new(start => 0);
  
  # Ensure that DFA state 0 is the one that corresponds to no
  # vertices in the input graph. This is an API convention and
  # does not have significance beyond that.
  my $r = { $o->s2n('') => {
    Combines => [],
    Accepts => $accepting->()
  } };
  
  # Ensure start state is 1 also as a convention
  $o->s2n($start_s);

  while (my ($src, $x) = each %$dfa) {
    while (my ($k, $dst) = each %{$x}) {
    
      # Merge dead states
      $src = '' unless $reachable{$src};
      $dst = '' unless $reachable{$dst};
      
      $r->{$o->s2n($src)}{NextOver}{$k} = $o->s2n($dst);

      my @src_combines = map { $m->n2s($_) } split/ /, $src;
      my @dst_combines = map { $m->n2s($_) } split/ /, $dst;
      
      $r->{$o->s2n($src)}{Combines} //= \@src_combines;
      $r->{$o->s2n($src)}{Combines} = [ sort { $a cmp $b }
        uniq (@{$r->{$o->s2n($src)}{Combines} // []}, @src_combines) ]
          if $src eq '';
      
      $r->{$o->s2n($dst)}{Combines} //= \@dst_combines;
      $r->{$o->s2n($dst)}{Combines} = [ sort { $a cmp $b }
        uniq (@{$r->{$o->s2n($dst)}{Combines} // []}, @dst_combines) ]
          if $dst eq '';

      $r->{$o->s2n($src)}{Accepts} //=
        0 + $accepting->(split/ /, $src);
      $r->{$o->s2n($dst)}{Accepts} //=
        0 + $accepting->(split/ /, $dst);
    }
  }
  
  return $r;
}

sub construct_dfa {
  my (%o) = @_;

  die unless ref $o{is_nullable};
  die unless ref $o{is_accepting};
  die unless ref $o{successors};
  die unless ref $o{get_label};
  die unless exists $o{start};

  _get_graph($o{start}, $o{get_label}, $o{is_nullable},
    $o{successors}, $o{is_accepting});

}


1;

__END__

=head1 NAME

Algorithm::ConstructDFA - Deterministic finite automaton construction

=head1 SYNOPSIS

  use Algorithm::ConstructDFA;
  my $dfa = construct_dfa(
    start        => $start_vertex,
    is_accepting => sub { grep { $_ eq $final_vertex } @_ },
    is_nullable  => sub {
      $g->has_graph_attribute($_[0], 'label')
    },
    successors   => sub { $g->successors($_[0]) },
    get_label    => sub {
      $g->get_graph_attribute($_[0], 'label') // ''
    },
  );

=head1 DESCRIPTION

This module provides a generic deterministic finite automaton
construction function. The input model is a graph with possibly
labeled (usually with "non-terminals") vertices. Edges in the
graph are always unlabeled.

=head1 FUNCTIONS

=over

=item construct_dfa(%options)

Construct a DFA using the given options.

=over

=item start

A start state for the initial configuration of the automaton.

=item is_accepting

A subroutine returning a boolean indicating whether this is an
accepting final state of the automaton. It is passed all the
vertices the states combines. For single-vertex acceptance, it
would usually C<grep> over the arguments. Having access to all
the states of the input automaton allows more complex acceptance
conditions (e.g. to compute the intersection of two graphs).

=item is_nullable

A subroutine returning a boolean indicating whether the automaton
can move past the supplied state without consuming any input.

=item successors

A subroutine that returns a list of all immediate successors of
the given vertex.

=item get_label

A subroutine that returns a caller-defined string representing what
kind of input is expected to move past the supplied vertex.

=back

The function returns the DFA as hash reference with integer keys. The
key C<0> is a non-accepting state with no transitions to other states
(the automaton would go into this state if the match has failed). The
key C<1> is the start state. The value of each entry is another hash
reference. As an example:

  '1':
    Accepts: 1
    Combines:
    - 0
    - 1
    - 2
    NextOver:
      a: 0
      b: 1

The C<Accepts> key indicates whether this is an accepting state. The
C<Combines> key provides access to the list of states in the input
automaton this DFA state corresponds to. The C<NextOver> field is the
transition table out of this state. This automaton matches any sequence
of zero or more C<b>s. The alphabet also includes the label C<a> but
the automaton moves from the start state over the label C<a> to the
non-accepting sink state C<0> and would never enter an accepting state
after that.

An exception to the rule above is when C<is_accepting> returns a true
value when passed no arguments (i.e., the automaton accepts when it is
in none of the states in the input automaton). Then state C<0> is made
an accepting state (and combines states from which the final vertex is
unreachable as before). This can be useful to compute complement graphs.

=back

=head1 EXPORTS

The function C<construct_dfa> by default.

=head1 AUTHOR / COPYRIGHT / LICENSE

  Copyright (c) 2014 Bjoern Hoehrmann <bjoern@hoehrmann.de>.
  This module is licensed under the same terms as Perl itself.

=cut

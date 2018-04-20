use application "polytope";

# parse the collection of combinatorial 3-spheres with up to 9 vertices provided by Moritz Fiersching at 
# https://page.mi.fu-berlin.de/moritz/polys/inscribe/
# for insertion into polydb
# call separetely for each dimension

use Data::Dumper;
use utf8;
no utf8;

sub parse_3spheres {

   my $filename = shift;

   my @a = ();
   my $count = 0;
   
   open(my $fh, "<", $filename) or die "Can't open < $filename: $!";

   while ( defined(my $line=<$fh>) ) {
      # remove spurious leftovers from sage
      if ( $line =~ m/QQ/ ) {
         $line =~ s/QQ\(([0-9]+)\)/$1/g;
      }
      
      # parse the initial part of a line
      # f-vector, f_03, realizability, incidences or vertices
      my ($v,$inc,$poly,$mat) = $line =~ m/\((.*)\)\s+([0-9]+)\s+([a-z-]+)\s+(?:type [0-9] )?\[[\[\(](.*?)[\)\]]\]/;
      
      # clean up 
      $mat =~ s/^[\[\(]//g;
      $mat =~ s/[\]\)]$//g;
      
      # convert to polymake: f-vector, #vertices
      my $fv = new Vector<Int>([split(",",$v)]);
      my $nv = $fv->[0];
      
      # convert to polymake: matrix
      my @rows = split(/[\]\)], [\[\(]/, $mat);
      my $splitrows = ();
      foreach (@rows) {
         my @arr= split(",",$_);
         push @$splitrows, \@arr;
      }
      
      # for 9 vertices we may have geometric data, so treat separately
      if ( $nv < 9 ) {
         
         # fix: for 8 vertices the index count starts at 1
         if ( $nv == 8 ) {
            foreach my $r (@$splitrows) {
               foreach my $e (@$r) {
                  $e--;
               }
            }
         }
         
         # convert to polymake: incidence matrix
         my $m = new IncidenceMatrix($splitrows);
         my $p=new Polytope(VERTICES_IN_FACETS=>$m, F_VECTOR=>$fv);
         # add some data
         $p->provide("N_VERTICES", "N_FACETS", "SIMPLE", "SIMPLICIAL","COMBINATORIAL_DIM");
         if ( $poly eq "polytope") {
            $p->attach("REALIZABLE",new Bool(1));
         } else {
            $p->attach("REALIZABLE",new Bool(0));
         }
         my $name = `printf "%06d" $count`;
         $name = $nv."V".$name;
         $p->name=$name;
         $count++;
         push @a, $p;
      } else {
         # 9 vertices
         if ( $poly eq "polytope") {
            my $m = new Matrix($splitrows);
            $m = ones_vector($m->rows)|$m;
            my $p=new Polytope(VERTICES=>$m, F_VECTOR=>$fv);
            $p->provide("VERTICES_IN_FACETS", "N_VERTICES", "N_FACETS", "SIMPLE", "SIMPLICIAL","COMBINATORIAL_DIM");
            $p->attach("REALIZABLE",new Bool(1));
            my $name = `printf "%06d" $count`;
            $name = $nv."V.".$name;
            $p->name=$name;
            $count++;
            push @a, $p;
         } else {
            my $m = new IncidenceMatrix($splitrows);
            my $p=new Polytope(VERTICES_IN_FACETS=>$m, F_VECTOR=>$fv);
            $p->provide("N_VERTICES", "N_FACETS", "SIMPLE", "SIMPLICIAL","COMBINATORIAL_DIM");
            $p->attach("REALIZABLE",new Bool(0));
            my $name = `printf "%06d" $count`;
            $name = $nv."V.".$name;
            $p->name=$name;
            $count++;

            # remove the initial part of the line: f-vector, incidences
            $line =~ s/.*type //;
            # get the type
            my ($type) = $line =~ m/^([1,2,3])/;
            # and remove it from the line
            $line =~ s/^[1,2,3] \[\((.*?)\)\] //;
            
            # get the partial chirotope from the end
            my ($chiro_string) = $line =~ m/\[\((?=\()(.*)\)\]$/;
            # remove it from the line
            $line =~ s/\Q$chiro_string$//;
            # split it
            my @chiro_arr = split(/\), \(/,$chiro_string);
            my $chiro = new Map<Set<Int>,String>;
            foreach (@chiro_arr) {
               my ($value) = $_ =~ m/(-?[1,0,None]+)$/;
               $_ =~ s/\), -?[1,0,None]+$//;
               $_ =~ s/\(//;
               my $key = new Set<Int>(split(",",$_));
               $chiro->{$key} = $value;
            }
            $p->attach("PARTIAL_CHIROTOPE",$chiro);
            
            # now it depends on the type what we can find in the remaining line
            if ( $type == 1) {
               # we find one set of three products p1, p2, p3 of two entries of the chirotope
               # in the set [ p1, -p2, p3 ] either all should be zero or both 1 and -1 should appear
               my (@relations) = $line =~ m/([-]?l[0-9_]+\*l[0-9_]+)/g;
               # check that there is no other way to certify this
               die if scalar(@relations) != 3;
               foreach ( @relations ) {
                  $_ =~ s/l/chi\(/g;
                  $_ =~ s/_/,/g;
                  $_ =~ s/\*/\) \* /;
                  $_ .= ")";
               }
               my $st = "[ ".$relations[0]." , ".$relations[1]." , ".$relations[2]." ]";

               $p->attach("TYPE",1);
               $p->attach("UNSATISFIED_GRASSMANN_PLUECKER_RELATION",$st);
            }
            if ( $type == 2 ) {
               # we find two sets of products p1, p2, p3 and q1, q2, q3 of two entries of the chirotope
               # where we do not know all velues of the chirtope but each set of products allows to deduce 
               # the value of the same entry of the chirotope, but they differ
               my ($contradicting_relation) = $line =~ m/\((.*)\)/;
               my ($contradicting_element_string) = $contradicting_relation =~ m/^(l[0-9_]+)/;
               my (@relations) = $line =~ m/([-]?l[0-9_]+\*l[0-9_]+)/g;
               
               # check that there is no other way to certify this
               die if scalar(@relations) != 6;
               foreach ( @relations ) {
                  $_ =~ s/l/chi\(/g;
                  $_ =~ s/_/,/g;
                  $_ =~ s/\*/\) \* /;
                  $_ .= ")";
               }
               $contradicting_element_string =~ s/l/chi\(/g;
               $contradicting_element_string =~ s/_/,/g;
               $contradicting_element_string =~ s/\*/\) \* /;
               $contradicting_element_string .= ")";
               my $st1 = new String("[ ".$relations[0]." , ".$relations[1]." , ".$relations[2]." ]");
               my $st2 = new String("[ ".$relations[3]." , ".$relations[4]." , ".$relations[5]." ]");
               my $s = new Array<String>([$st1,$st2]);

               $p->attach("TYPE",2);
               $p->attach("CONTRADICTING_ELEMENT",$contradicting_element_string);
               $p->attach("CONTRADICTING_GRASSMANN_PLUECKER_RELATIONS",$s);
            }
            if ( $type == 3 ) {
               my ($constraint_string) = $line =~ m/Constraints:, (.*), Variables/;
               my $constraints = new Array<String>(split(",",$constraint_string));

               my ($variable_string) = $line =~ m/Variables:, \{(.*)\}/;
               my @variable_arr = split(/, \(/, $variable_string);
               my $variables = new Map<String,String>;
               foreach (@variable_arr) {
                  my ($key) = $_ =~ m/(x_[0-9]+)/;
                  $_ =~ s/\(//;
                  $_ =~ s/\).*//;
                  $variables->{$key} = "[".$_."]";
               }

               $p->attach("TYPE",3);
               $p->attach("INFEASIBLE_LP",$constraints);
               $p->attach("VARIABLE_NAMES",$variables);
            }
            push @a, $p;
         }
      }
      
      # insert into db in chunks of 1000
      if ( $count % 1000  == 0 ) {
         print $count, "\n";
         my $b = new Array<Polytope>(@a);
         db_insert($b,db=>"Polytopes",collection=>"SmallSpheresDim4",type_information_key=>"small_spheres",nonew=>1);
         @a = ();
      }
   }
   my $b = new Array<Polytope>(@a);
   db_insert($b,db=>"Polytopes",collection=>"SmallSpheresDim4",type_information_key=>"small_spheres",nonew=>1);
   close($fh);
}
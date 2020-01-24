#!/pkg/bin/perl -w
#use diagnostics
# brownhapSAT1.pl
#
# January 7, 2020 modify to remove the objective function from the ILP formulation, and only test
# if the target is achievable. However, instead of writing this in the simplest ILP way, we write it
# in a way that is similar to the way that the CNF clauses express this. The reason for doing this
# is to be able to then automatically convert the ILP formulation to a CNF formulation, which is
# done with the programs compactlp.pl and remconvertNc.pl.
#
# Call the program on a command line as: perl brownhapSAT1.pl input_matrix target
# The first line of the input_matrix has the name of the matrix (not used in this program).
# The second line has the number of rows and the number of columns, with a space between the
# numbers. See the file "datagperm" for an example of an input matrix. The optimal solution value
# for datagperm is 14 - try it out with both ILP and SAT-solving.

# Dec. 28, 2019.  brownhapSAT.pl 
# The program is extended to also creates the CNF formula to test if a target number of distinct
# haplotypes is possible.  
# derived from brownhap.pl
#
#dg
#brownhap.pl developed by DG  11/7/2004
# This implements the generation of the ILP for maximum parsimony haplotyping as
# specified in the Brown WABI paper. 
#

print "IGNORE the above NAME warnings \n";

%index = ();
%haps = ();
%bin = ();
@pairconsts = ();
$hapcount = $tot = $numgens = 0;
$input = $ARGV[0];
open IN, "$input";
open OUT, ">$input.lp";
open SATOUT, ">tempSAT";
open OUTKEY, ">$input.KEY";
open SAT_FINAL, ">$input.SAT";
$target = $ARGV[1];

$line1 = <IN>;
$line2 = <IN>;
($gencount, $sitecount) = split (/ /,$line2);
print "$gencount, $sitecount\n";
$hapcount = 2*$gencount;

@gens = <IN>; # this is the genX file.
# print OUT "@gens";

 print OUT "minimize 0 \n";
# print OUT "minimize \n";
# foreach $i (1...$hapcount) {
#   print OUT "+ U($i) ";
#   if (0 == $i % 8) {
#     print OUT "\n";
#   } 
# } 

 print OUT "\n st \n";


$SATinteger = 0;
%ySATvariable = ();
%ySATintegervar = ();
%dSATvariable = (); # indexed by a pair of row indices, with value equal to
                    # SATinteger.
%dSATintegervar = (); # indexed by a SATinteger, with value equal to the pair of
                      # row indices associated with that SATinteger
%USATvariable = ();
%USATintegervar = ();
%TUSATvariable = ();
%TUSATintegervar = ();
$clauses = "";

$clausecount = 0;

 $i = 1;
 foreach $line (@gens) {
 chomp $line;
 $line =~ tr/ //d;
 $s = (2*$i);
 $f = $s -1;

 @entry = split (//,$line);
  foreach $k (1..$sitecount) { 
  
     $index1 = "$f,$k";
     $var{$index1} = 1;
#    print "$index1\n";

     $SATinteger++;
     $ySATvariable{"$index1"} = $SATinteger;
     $ySATintegervar{$SATinteger} = $index1;

     $index2 = "$s,$k";
     $var{"y$index2"} = 1;
#     print "$index2\n";

     $SATinteger++;
     $ySATvariable{"$index2"} = $SATinteger;
     $ySATintegervar{$SATinteger} = $index2;
 

   if ($entry[$k-1] eq '2') {
     print OUT "y$index1 + y$index2 = 1\n";
     print SATOUT "$ySATvariable{$index1} $ySATvariable{$index2} 0 \n";
     print SATOUT "-$ySATvariable{$index1} -$ySATvariable{$index2} 0 \n";
     $clausecount = $clausecount + 2;
   }
   elsif ($entry[$k-1] eq '1') {
     print OUT " y$index1 = 1\n y$index2 = 1\n";
     print SATOUT "$ySATvariable{$index1} 0 \n $ySATvariable{$index2} 0 \n";
     $clausecount = $clausecount + 2;
  }
   elsif ($entry[$k-1] eq '0') {
     print OUT " y$index1 = 0\n y$index2 = 0\n";
     print SATOUT "-$ySATvariable{$index1} 0 \n -$ySATvariable{$index2} 0 \n";
     $clausecount = $clausecount + 2;
  }

 } 
 $i++;
}

foreach $i (1..$hapcount) {
   $im1 = $i - 1;
    foreach $j (1..$im1) {
     foreach $k (1..$sitecount) {
      $indexi = "$i,$k";  # for scanning across row i
      $indexj = "$j,$k";  # for scanning across row j
      $index = "$i,$j";  # a pair of row indices
      if (! defined $dSATvariable{$index}) {
          $SATinteger++;
          $dSATvariable{$index} = $SATinteger;
          $dSATintegervar{$SATinteger} = $index;
      }
      if (! defined $ySATvariable{$indexi}) {
         $SATinteger++;
         $ySATvariable{$indexi} = $SATinteger;
         $ySATintegervar{$SATinteger} = $indexi;
      } 
      if (! defined $ySATvariable{$indexj}) {
         $SATinteger++;
         $ySATvariable{$indexj} = $SATinteger;
         $ySATintegervar{$SATinteger} = $indexj;
      } 

        print OUT "d$i,$j - y$i,$k + y$j,$k >= 0\n";
        print OUT "d$i,$j - y$j,$k + y$i,$k >= 0 \n";



        print SATOUT "$SATinteger -$ySATvariable{$indexi} $ySATvariable{$indexj} 0 \n"; 
        print SATOUT "$SATinteger $ySATvariable{$indexi} -$ySATvariable{$indexj} 0 \n"; 
        $clausecount = $clausecount + 2;
    }
   }
}

foreach $i (1..$hapcount) {
   $SATinteger++;
   $USATvariable{$i} = $SATinteger;
   $USATintegervar{$SATinteger} = "U($i)";
   $Uclause =  "$SATinteger ";

   $twomi = 2 - $i;
   print OUT "U($i) "; 

   $im1 = $i - 1;
    foreach $j (1..$im1) {
    print OUT "- d$i,$j ";
    $index = "$i,$j";
    $Uclause .= "-$dSATvariable{$index} ";

    }
    print OUT ">= $twomi\n";
    print SATOUT "$Uclause 0 \n";
    $clausecount++;
}


# let TU($i,$k) mean that the total number of unique haplotypes before haplotype i is examined is at least k. 
# Then TU($i,$k) AND U($i) implies TU($i+1,$k+1).
# We need one of these clauses for each i from 2 to hapcount+1, and for each i, k must vary from 1 to i-1. 
# Also, need that TU(2,1) is set true.

print SATOUT "c Clauses to count the number of distinct haplotypes \n";
# first set up the TU variables and their corresponding integers.

$SATinteger++;     # we don't need a TU variable for haplotype 1, and we know that TU(2,1) should be
                   # set true, because haplotype 1 is unique, i.e. U(1) is true.
$TUSATvariable{"2,1"} = $SATinteger; 
$TUSATintegervar{$SATinteger} = "2,1";
$clauses = "$SATinteger 0 \n";
$clausecount++;

foreach $i (3 .. $hapcount+1) {  # need a variable for hapcount+1 because the last haplotype might be unique.
     foreach $k (1 .. $i-1) {
        $SATinteger++;
        $index = "$i,$k";
        $TUSATvariable{$index} = $SATinteger;
        $TUSATintegervar{$SATinteger} = $index;
        $bin{"TU($index)"} = 1;
     }
}

$TUstring = "U(1) = 1 \n TU(2,1) = 1 \n";
# Now create the needed clauses
foreach $i (2 .. $hapcount) {
     foreach $k (1 .. $i-1) {
        $index = "$i,$k";
        $ip1 = $i + 1;
        $kp1 = $k + 1;
        $v1 = $TUSATvariable{$index};
        $v2 = $USATvariable{$i};
        $v3 = $TUSATvariable{"$ip1,$kp1"};
        $clauses .= "$v3 -$v1 -$v2 0 \n"; #TU(i,k) and U(i) implies TU(i+1,k+1)
        $clausecount++;
        $TUstring .= "TU($i,$k) + U($i) - TU($ip1,$kp1) <= 1 \n";

        foreach $j ($ip1 ... $hapcount + 1) {
            $v4 = $TUSATvariable{"$j,$k"}; #TU(i,k) implies TU(j,k) for all j > i
            $clauses .= "$v4 -$v1 0 \n";
            $clausecount++; 
            $TUstring .= "TU($index) - TU($j,$k) <= 0 \n";
        }

     }
}

print SATOUT "$clauses";
$tp1 = $target + 1;
$hp1 = $hapcount + 1;
$integer = $TUSATvariable{"$hp1,$tp1"};
print SATOUT "-$integer 0 \n";
$clausecount++;

print OUT "$TUstring \n";
print OUT "TU($hp1,$tp1) = 0 \n";

print OUT "binaries\n";
foreach $i (1..$hapcount) {
  print OUT "U($i)\n";
  foreach $k (1..$sitecount) {
    print OUT "y$i,$k\n"
  }
} 

foreach $i (1..$hapcount) {
   $im1 = $i - 1;
    foreach $j (1..$im1) {
    print OUT "d$i,$j\n";
    }
}

foreach $index (sort keys %bin) {
    print OUT "$index \n";
}
print OUT "end\n";

print OUTKEY "y variables \n";
foreach $integer (sort {$a <=> $b} keys %ySATintegervar) {
    print OUTKEY "$integer y$ySATintegervar{$integer}\n";
}

print OUTKEY "d variables \n";
foreach $integer (sort {$a <=> $b} keys %dSATintegervar) {
    print OUTKEY "$integer d$dSATintegervar{$integer}\n";
}

print OUTKEY "U variables \n";
foreach $integer (sort {$a <=> $b} keys %USATintegervar) {
    print OUTKEY "$integer $USATintegervar{$integer}\n";
}

print OUTKEY "TU variables \n";
foreach $integer (sort {$a <=> $b} keys %TUSATintegervar) {
    print OUTKEY "$integer TU($TUSATintegervar{$integer})\n";
}

print SAT_FINAL "p cnf $SATinteger $clausecount \n";
close (SATOUT);
open SATOUT, "tempSAT";
while ($line = <SATOUT>) {
   print SAT_FINAL "$line";
}
close(SAT_FINAL);


print "The number of variables and clauses: $SATinteger  $clausecount \n\n";
print "The ILP formulation is in file $input.lp, and the CNF formulation is in file $input.SAT. \n";
print "The ILP formulation is ready for solution by ILP solvers from Gurobi or Cplex. \n";
print "The CNF formulation is in Dimacs format, and hence ready for any SAT-solver that uses the \n";
print "Dimacs format (which is most of them). We have used SAT-solvers plingeling and glucose-syrup. \n ";

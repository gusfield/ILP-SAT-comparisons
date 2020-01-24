# SATsimhistory.pl October 6,  2019
#
# This generates an ILP that simulates the workings of the original
# history-bound alg. The choices I have made in this particular ILP are to
# make it as easily converted to SAT as possible. Interwoven now is code to
# create a CNF formula expressing the proposition that the history bound is <= a given bound.
# For technical reasons, there is a phase 0 and a phase n+1, but no operations are done in those phases.
#
#
# The input has three parameters, the first is the number of characters in the input matrix; the second
# is the file where the matrix is held; and the third is the target for the CNF. The ILP computes
# the actual history bound and so it's computation does not use the target.

# R(i,k) = 1 means that row i is removed by a Dr operation in phase k, i.e., by a merge
# RO(i,k) = 1 means that row i is removed by a Dt operation in phase k, i.e., by an arbitrary row removal
# C(j,k) = 1 means that column j is removed by a Dc operation in phase k
# TRO(c,k) = 1 means that at least c Dt operations were done before phase k.
# TR(i,k) = 1 means that row i has been deleated before phase k, either by a Dr or a Dt operation
# TC(j,k) = 1 means that column j was removed  by a Dc operation before phase k
# M(i,iprime,k) = 1 means that rows i and iprime are merged in phase k

my $m =  $ARGV[0];

@lines = ();
$Rconstraints = "";
$Cconstraints = "";
$Dtconstraints = "";
%bin = ();
%SATvariable = (); # This is a hash indexed by ILP variables, with value equal to the integer used to encode that variable in Dimacs format.

open (IN, $ARGV[1]);
open (OUT, ">$ARGV[1].lp");
open (SATOUT, ">sat_temp");
open (SAT_FINAL, ">$ARGV[1].SAT");
open (SAT_KEY, ">$ARGV[1].KEY");

$target = $ARGV[2];

while ($line = <IN>) {

  push(@lines, $line);
  print "$line";
  chomp $line;
  } # end while line = <IN>
$n = @lines;
#print SATOUT "c rows and cols: $n, $m\n";  # the number of rows and colums in the input matrix

%inline = ();


$b = $m + $n; # b is a bound on the number of phases in the ILP. In each phase at least one row or one col. is removed. Later we will
              # substitute a better bound for b.

$SATinteger = 1;
print OUT "Minimize \n";
foreach $i (1 .. $n) {   # every row can be deleted in at most one phase, either by a Dr or a Dt operation.
    foreach $k (1 .. $b) {
       $Rconstraints .= "+ R($i,$k) +  RO($i,$k) "; 
       print OUT "+ RO($i,$k) "; # building up the objective function, minimizing the number of Dt operations.

       $bin{"R($i,$k)"} = 1;
       $SATvariable{"R($i,$k)"} = $SATinteger;
       $SATinteger++;
       $bin{"RO($i,$k)"} = 1;
       $SATvariable{"RO($i,$k)"} = $SATinteger;
       $SATinteger++;
    }
    $Rconstraints .= "<= 1 \n\n";
}


$clausecount = 0;
#print SATOUT "c clauses for the R and RO variables \n";
foreach $i (1 .. $n) {
	foreach $k (1 .. $b-1) {
		foreach $kprime ($k + 1 .. $b) {   # create the SAT clauses that say that for each i, the operation R(i,k) can only
			                           # be done in one phase k. Similarly the operation RO(i,k) can only be done in
						   # one phase k.
			$v1 = $SATvariable{"R($i,$k)"};
			$v2 = $SATvariable{"R($i,$kprime)"};
			print SATOUT "-$v1 -$v2 0 \n";
                        $clausecount++;

			$v3 = $SATvariable{"RO($i,$k)"};
			$v4 = $SATvariable{"RO($i,$kprime)"};
			print SATOUT "-$v3 -$v4 0 \n";
                        $clausecount++;
		}
	}

	foreach $k (1 .. $b) {
		foreach $kprime (1 .. $b) {   # create the SAT clauses that say that for each i, it is 
		                              #	not permitted that an R(i,k) and an RO(i,kprime) both occur, including the case
                                              # that the two phases are the same.
			$v1 = $SATvariable{"R($i,$k)"};
			$v2 = $SATvariable{"RO($i,$kprime)"};
			print SATOUT "-$v1 -$v2 0 \n";
                        $clausecount++;

		}
	}
} # end foreach $i

print OUT "\n st \n\n";
print OUT "$Rconstraints";

print SATOUT "c clauses for the C(j,k) operations \n";
foreach $j (1 .. $m) {     # in the ILP formulation, each column must be deleted by a Dc operation in exactly one phase.
                           #
                           # the SAT clauses here only establish that every column must be removed. The converse is implemented at the end of the program
   $clause = "";
   foreach $k (1 .. $b) {
        $Cconstraints .= " + C($j,$k) ";
        $SATvariable{"C($j,$k)"} = $SATinteger;
	$clause .= "$SATinteger ";
#        print SATOUT "SATinteger in creation of C variables j, k, b, SATinteger: $j, $k, $b, $SATinteger \n";
        $SATinteger++;
   }
   $Cconstraints .= "= 1 \n\n";
   print SATOUT "$clause";
   print SATOUT "0\n";
   $clausecount++;
} # end of foreach j

#print SATOUT "At the end of the creation of C variables: $SATinteger \n";
print OUT "$Cconstraints";

foreach $j (1 .. $m) {         # these SAT clauses establish that no column can be removed in two different phases.
     foreach $k (1 .. $b-1) {
        foreach $kprime ($k + 1 .. $b) {
		$v1 = $SATvariable{"C($j,$k)"};
		$v2 = $SATvariable{"C($j,$kprime)"};
		print SATOUT "-$v1 -$v2 0 \n";
                $clausecount++;
        }
      }
}



# Now we create inequalities that bound the number of Dt operations we do. For a pure ILP formulation, this would not be necessary because
# the objective function is to minimize the number of Dt operations. But for SAT we need to have a mechanism to count (and bound) the number
# of Dt ops. Here we have choices. We could allow any number of Dt operations per phase and use the tree trick with all of the RO(i,k) variables
# to bound the total number of Dt operations. Or, we can restrict the number of Dt operations to one per phase, and have a simpler counting variable
# that says that if there were (at least) t Dt ops. before phase k, and a Dt op. is done in phase k, then another variable is set that says that (at least) 
# t+1 Dt ops were done before phase k+1.
# Also, have inequalities that say that if at least t Dt ops were done before phase k, then  at least t Dt ops are done before phase k+1. 
# Lets say that TRO(c,k) is the binary variable with the interpretation that at least c Dt operations were done before phase k, and recall that b is
# an upper bound on the number of phases needed. Then, we can limit the total number of Dt operations done in a scenario to c by the single clause 
# not(TRO(c+1,b+1)).
# I am going to  take the latter approach because the tree trick is too hard to program.

print "At the start of the creation of TRO variables: $SATinteger \n";
       $SATvariable{"TRO(1,1)"}  = $SATinteger; #DG october 12, 2019
       print SATOUT "-$SATinteger 0 \n";
       $SATinteger++;
#       $SATvariable{"TRO(0,1)"} = $SATinteger;
#       print SATOUT "$SATinteger 0 \n";
#       $SATinteger++;
#       $clausecount = $clausecount + 2;
       $clausecount = $clausecount + 1;

foreach $c (0 .. $n) {     # create the needed SAT variables
     foreach $k ($c+1 .. $b+1) {
       $SATvariable{"TRO($c,$k)"}  = $SATinteger;
       $SATinteger++;
     }
}


 # now create the inequalities that keep count of the number of Dt operations that were done. TRO(c,k) = 1 means that
 # at least c Dt operations were done before phase k.

$TROconstraints = "TRO(0,1) = 1 \n";  # at most 0 Dt operations were done before phase 1. 

print SATOUT "c clauses for the TRO variables and joint TRO RO statements\n";
$ROconverse = "";
$vconverse = "";

foreach $count (0 .. $n-1) {  # DG Sept. 29, 2019, change n to n-1.
    $cp1 = $count + 1;
    foreach $k ($count + 1 .. $b) {   
         $ROstring = "";
         $bin{"TRO($count,$k)"} = 1; 
         $vstring = "";
         $kp1 = $k + 1;
         $TROconstraints .= "TRO($count,$k) - TRO($count,$kp1) <= 0 \n"; # if at least count Dt operations were done before phase k, then
                                                                         # at least count Dt operations were done before phase k+1.

         $v1 = $SATvariable{"TRO($count,$k)"};
         $v2 = $SATvariable{"TRO($count,$kp1)"};
#         print SATOUT "$v2 -$v1 0: $count, $k, $kp1 \n";
          print SATOUT "$v2 -$v1 0 \n";
         $clausecount++;

         $TROconstraints .= "TRO($cp1,$kp1) - TRO($count,$k) <= 0 \n"; # the count of Dt operations can only go up by 1 in each phase. That is, if
                                                                       # there are at least count+1 Dt operations before phase kp1, then there were
                                                                       # at least count Dt operations before phase k.
            $bin{"TRO($count,$kp1)"} = 1;
            $v1 = $SATvariable{"TRO($count,$k)"};
            $v2 = $SATvariable{"TRO($cp1,$kp1)"};
            print SATOUT "$v1 -$v2 0 \n";
            $clausecount++;

            foreach $i (1 .. $n) {
                $TROconstraints .= "TRO($count,$k) + RO($i,$k) - TRO($cp1,$kp1) <= 1 \n"; # if at least count Dt operations were done before phase k
                                                                                          # and another Dt operation is done in phase k, then
                                                                                          # at least count+1 Dt operations were done before phase k+1.
                $ROstring .= "- RO($i,$k) "; # build up a string of all the n possible Dt operations
                $bin{"RO($i,$k)"} = 1;
                $bin{"TRO($cp1,$kp1)"} = 1;

                $v  = $SATvariable{"RO($i,$k)"}; # build up a string of all the n possible variables indicating a Dt operation in phase k
                $vstring .= "$v ";

                $v1 = $SATvariable{"TRO($cp1,$kp1)"};
                $v2 = $SATvariable{"TRO($count,$k)"};
                $v3 = $SATvariable{"RO($i,$k)"};
                print SATOUT "$v1 -$v2 -$v3 0 \n";
                $clausecount++;
            }


             # Now create inequalities for the converse: If TRO(count,kp1) - TRO(count,k) = 1, then there must have been a Dt operation in phase k.
             $v1 = $SATvariable{"TRO($count,$kp1)"};
             if ($count > 0) {
                  $ROconverse .= "TRO($count,$kp1) - TRO($count,$k) " .  $ROstring . " <= 0 \n";
                  $vconverse  .= "$vstring-$v1 $v2 0 \n";
                  $clausecount++;
             }
     } # end of foreach k
   $v1 = $SATvariable{"TRO(0,1)"};
   print SATOUT "$v1 0 \n";
   $clausecount++;
}

print OUT "$TROconstraints \n";
print OUT "$ROconverse \n";
print SATOUT "c clauses for the converse \n";
print SATOUT "$vconverse";


# now create the inequalities that record which rows have been deleted before phase k.
# TR(i,k) = 1 means that row i has been deleated before phase k, either by a Dr or a Dt operation.

$TRconstraints = "";
foreach $i (1 .. $n) {
    $TRconstraints .= "TR($i,1) = 0 \n";
    $bin{"TR($i,1)"} = 1;
    foreach $k (2 .. $b) {
         $kp1 = $k + 1;
         $km1 = $k - 1;
         $TRconstraints .= "TR($i,$k) - TR($i,$kp1) <= 0 \n";  # if row i has been removed before phase k, then it has been removed before phase k+1.
         $TRconstraints .= "RO($i,$km1) - TR($i,$k) <= 0 \n";  # if row i is removed by a Dt operation in phase k-1, then it has been removed before phase k.
         $TRconstraints .= "R($i,$km1) - TR($i,$k) <= 0 \n";   # if row i is removed by a Dr operation in phase k-1, then it has been removed before phase k.
         $bin{"TR($i,$k)"} = 1;
         $bin{"TR($i,$kp1)"} = 1;
         }
   $TRconstraints .= "\n";
}

print OUT "$TROconstraints";
print OUT "$TRconstraints";


# Now we create the needed variables for the related clauses for the SAT formulation. We also take care of the special case of TR($i,1) in this block.
$TRclauses = "";
foreach $i (1 .. $n) {
   $SATvariable{"TR($i,1)"} = $SATinteger;
   $TRclauses .= "-$SATinteger 0 \n";   # create the clause that says TR($i,1) is false.
   $SATinteger++;
   $clausecount++;

   $bp1 = $b + 1;
   foreach $k (2 .. $bp1) {
      $SATvariable{"TR($i,$k)"} = $SATinteger;
      $SATinteger++;
   }
}

foreach $i (1 .. $n) {    # now create the clauses corresponding to the three constraints created above in TRconstraints
   foreach $k (1 .. $b) {
         $kp1 = $k + 1;
         $v1 = $SATvariable{"TR($i,$k)"};

         $v2 = $SATvariable{"TR($i,$kp1)"};
         $TRclauses .= "$v2 -$v1 0 \n";
         $clausecount++;

         $v1 = $SATvariable{"RO($i,$k)"};
  #       $TRclauses .= "$v1 -$v2 0 \n";  # DG Oct. 10, 2019
         $TRclauses .= "$v2 -$v1 0 \n";
         $clausecount++;

         $v1 = $SATvariable{"R($i,$k)"};
         $TRclauses .= "$v2 -$v1 0 \n";
         $clausecount++;
   }
} 

print SATOUT "c clauses to encode the basic facts of TR variables \n";         
print SATOUT "$TRclauses";



# Now we examine the input matrix M to find, for each column j, the location of the 1s in column j. 

foreach $j (1 .. $m) { # initialize a hash, ones,  indexed by column numbers. For each column the value will be a list.
   $ones{$j} = [];
}

$i = 0;
foreach $line (@lines) {  # scan a line of input and build up the hash called ones.
     $i++;
     @bits   = split (//,$line); 
     foreach $j (1 .. $m) {
        if ($bits[$j-1] == 1) {
           push (@{$ones{$j}}, $i);
        }
     }
}
        

$Cconstraints = ""; 
                    # implement the condition: Column j is removed in phase k only if there is at most one 1 in the column. (We also want to remove j if
                    # col. j contains only 1s. - this has not been done as of Oct. 8, in either the ILP or in SAT).

                    # Also create the inequalies that say that if column j is removed in phase k, then variable TR(j,k+1) should be set to 1. That
                    # variable records the fact that if column j is removed in phase k, then it has been removed by phase k+1.


$Cclauses = "";

$TCconstraints = "";
$TCclauses = "";

foreach $j (1 .. $m) {
    $num_ones = @{$ones{$j}};
    $nom1 = $num_ones - 1;
    $nom2 = $num_ones - 2;
#    print SATOUT "For column $j there are $num_ones ones, and they are in rows: @{$ones{$j}} \n";


    foreach $k (1 .. $b) {  
       $kp1 = $k + 1;

       # create the inequalities that for every column j, if column j is removed in phase k, then there is at most one row in col. j
       # that has a 1 in it.
       foreach $i (@{$ones{$j}}) {
           $Cconstraints .= "+ TR($i,$k) ";
       }
       $Cconstraints .= "- $nom1 C($j,$k) >= 0 \n";

       $Cconstraints .= "C($j,$k) - TC($j,$kp1) <= 0 \n"; # if col. j is removed in phase k, then set the TC variable to record that col. j was removed
                                                         # before entry into phase k+1.

       $Cconstraints .= "TC($j,$k) - TC($j,$kp1) <= 0 \n\n"; # if col. j was removed before entry into phase k, then it was removed before entry into phase k+1.

       $bin{"C($j,$k)"} = 1;
       $bin{"TC($j,$k)"} = 1;
       $bin{"TC($j,$kp1)"} = 1;

       $TCconstraints .= "TC($j,$k) ";   # Create inequalities that if the TC(j,k) variable is set to 1, meaning that col. j has been removed before entry into
                                    # phase k, then column j was removed in some specific phase from 1 to k-1. DG this look redundant with the above clauses.


       foreach $q (1 .. $k - 1) {
           $TCconstraints .= "- C($j,$q) ";
       }
       $TCconstraints .= "<= 0 \n";
    }
    $TCconstraints .=  "\n";
}

print OUT "\n $Cconstraints";
print OUT "\n";
print OUT "$TCconstraints \n\n";

foreach $j (1 .. $m) {
    $SATvariable{"TC($j,1)"} = $SATinteger; # column j cannot be removed before phase 1, i.e. that TC(j,1) is false for all j.
    print SATOUT "-$SATinteger 0\n";
    $SATinteger++;
    $clausecount++;

    foreach $k (2 .. $b+1) {  # to create the correct SAT clauses, we need k to go to b+1.
    $km1 = $k - 1;


  # Create inequalities that if the TC(j,k) variable is set to 1, meaning that col. j has been removed before entry into
  # phase k, then column j was removed in some specific phase q from 1 to k-1.
     
       $SATvariable{"TC($j,$k)"} = $SATinteger;  
       $v1 = $SATinteger;
       $SATinteger++;

#       print SATOUT "v1 for TC($j,$k)  $v1 \n";
       $v2string = "";
       foreach $q (1 .. $k - 1) {
           $var = $SATvariable{"C($j,$q)"};
           $v2string .= "$var ";
       }
       $TCclauses .= "-$v1 $v2string";
       $TCclauses .= "0 \n";
       $clausecount++;
       $v3 = $SATvariable{"TC($j,$km1)"};
#       print SATOUT "$k, $km1, $j, $v3 \n";
       $TCclauses .= "$v1 -$v3 0 \n";    # if column j was removed before entry into some phase k-1, then it was removed before entry into phase k 
       $clausecount++;
    }
}

print SATOUT "c create SAT clauses for  TC(j,k) => C(j,1) or C(j,2) or ... or C(j,k-1).\n";
print SATOUT "$TCclauses";

print SATOUT "c clauses for the joint C and TR variables \n";
foreach $j (1 .. $m) {  # create the C variables for the clauses for the assertion that if column j is removed in phase k, then there is at most one row in col. j.
                        # with a value of 1.
  
  foreach $k (1 .. $b) {
       $kp1 = $k + 1;
       foreach $i (@{$ones{$j}}) {   # create the clauses for the above assertion. This is done by the logic that if col. j is removed in phase k,
                                     # and rows i and i' have entry 1 in col. j, then at least one of rows i or i' has been removed by phase k. This
                                     # is asserted for every such pair of rows i, i'.
           foreach $iprime (@{$ones{$j}}) {
               if ($i < $iprime) {
                  $v1 = $SATvariable{"TR($i,$k)"};
                  $v2 = $SATvariable{"TR($iprime,$k)"};
                  $v3 = $SATvariable{"C($j,$k)"};
                  print SATOUT "$v1 $v2 -$v3 0 \n";
                  $clausecount++;
               }
            }
        }

       # If col. j is removed in phase k > 1, then set the TC variable to record that col. j was removed before phase k+1
            $v3 = $SATvariable{"C($j,$k)"};
            $v4 = $SATvariable{"TC($j,$kp1)"}; 
            print SATOUT "$v4 -$v3 0 \n";
            $clausecount++;
    } # end of foreach k
} # end of foreach j
 

$Mconstraints = "";    # Create inequalities to implement the logic that if rows i and iprime > i are merged, then all the columns where the two
                       # rows differ must have been deleted. Also, merging i and iprime results in the removal of iprime (by convension, the row, i or i',
                       # with the largest index is removed) by a Dr operation. 

$MDstring = "";   # String for the SAT clauses corresponding the the Mconstraints.
              
$M1constraints = ""; # Create inequalities to implement the logic that at most one merge operation can be done in any phase.
$MD1string = "";   # String for the SAT clauses corresponding the the M1constraints.


foreach $k (1 .. $b) {
  foreach $i (1 .. $n-1) {
    foreach $iprime ($i+1 .. $n) {
          $SATvariable{"M($i,$iprime,$k)"} = $SATinteger;
          $SATinteger++;
          @bits1 = split(//,$lines[$i - 1]);
          @bits2 = split(//,$lines[$iprime - 1]);
              foreach $j (1 .. $m) {
                  if ($bits1[$j-1] != $bits2[$j-1]) {
                      $Mconstraints .= "M($i,$iprime,$k) - TC($j,$k) <= 0 \n"; # if rows i and i' are merged in phase k, then column j must have
                                                                               # been deleted before phase k, for each column j where rows i and
                                                                               # i' differ.

                      $v1 = $SATvariable{"TC($j,$k)"};
                      $v2 = $SATvariable{"M($i,$iprime,$k)"};
                      $MDstring .= "$v1 -$v2 0 \n"; # create the clauses corresponding to the Mconstraints inequalities above.
                      $clausecount++;
                  }
               }

       $Mconstraints .= "M($i,$iprime,$k) - R($iprime,$k) <= 0 \n";  # if rows i and i' are merged in phase k, then remove row i' in phase k by a Dr operation.
       
       $v1 = $SATvariable{"R($iprime,$k)"};  # create the SAT clauses corresponding to the ILP constraints in Mconstraints here.
       $v2 = $SATvariable{"M($i,$iprime,$k)"};
       $MDstring .= "$v1 -$v2 0 \n";
       $clausecount++;

       $M1constraints .= "+ M($i,$iprime,$k) ";  # create the constraints that say rows i and i' can only be merged in one phase.
       $bin{"M($i,$iprime,$k)"} = 1;

    }
  }
  $M1constraints .= "<= 1 \n";
}

# create the corresponding SAT clauses here. That is rows i and i' can only be merged in one phase. Put them into MD1string.
foreach $k (1 .. $b-1) {
  foreach $kprime ($k+1 ..  $b) {
     foreach $i (1 .. $n-1) {
         foreach $iprime ($i+1 .. $n) {
                       # want to iplement $M($i,$iprime,$k) -> Not $M($i,$iprime,$kprime) 
               $v1 = $SATvariable{"M($i,$iprime,$k)"};
               $v2 = $SATvariable{"M($i,$iprime,$kprime)"};
               $MD1string .= "-$v1 -$v2 0 \n";
               $clausecount++;
         }
     }
  }
}
  

print OUT "$Mconstraints \n";
print OUT "\n $M1constraints \n";

print SATOUT "c clauses for the constraints that if rows i and i' are merged in phase k, then all columns where the two rows differ have been deleted.\n";
print SATOUT "c Also, if rows i and i' are merged in phase k, then row i' is removed by a Dr operation in phase k.\n";
print SATOUT "$MDstring";

print SATOUT "c clauses for the constraints that rows i and i' can only be merged in one phase. \n";
print SATOUT "$MD1string";



# Covering the other direction, if a row is removed by a Dr operation, then it must
# have merged with another row in the same phase.

$R1constraints = ""; 
$R1SATconstraints = "";
print SATOUT "c create the clauses that relate Merging to Removing and TRemoving \n";

foreach $k (1 .. $b) {
    $R1constraints .= "+ R(1,$k) "; # create the constraints that say that row 1 cannot be removed by a Dr operation.
    $v1 = $SATvariable{"R(1,$k)"};
    $R1SATconstraints .= "-$v1 0\n";
    $clausecount++;

  foreach $iprime (2 .. $n) {
       $MRconstraints = "R($iprime,$k) "; # if row i' is removed in phase k
       $MRSATconstraints = ""; 
       foreach $i (1 .. $iprime - 1) {
          $MRconstraints .= "- M($i,$iprime,$k) "; # then it must have been merged in phase k with a row i < i'
          $v1 = $SATvariable{"M($i,$iprime,$k)"};
          $MRSATconstraints .=  "$v1 ";
          
          print OUT "M($i,$iprime,$k) + TR($i,$k) <= 1 \n";  # if row i has been removed before phase k, then rows i and i' cannot be merged in
                                                             # phase k
          $v1 = $SATvariable{"M($i,$iprime,$k)"};
          $v2 = $SATvariable{"TR($i,$k)"};
          print SATOUT "-$v1 -$v2 0\n";
          $clausecount++;

          print OUT "M($i,$iprime,$k) + TR($iprime,$k) <= 1 \n";  # if row i' has been removed before phase k, then rows i and i' cannot be merged in
                                                                  # phase k.
          $v2 = $SATvariable{"TR($iprime,$k)"};
          print SATOUT "-$v1 -$v2 0\n";
          $clausecount++;
       }

     $MRconstraints .= "<= 0 \n";   # DG why is this not = 0? It works with =, but it is slower. Why?
    # $MRconstraints .= "= 0 \n";   # DG try it, Oct. 7, 2019
     print OUT "$MRconstraints \n";
     $v1 = $SATvariable{"R($iprime,$k)"};  # if row i' is removed in phase k
     print SATOUT "$MRSATconstraints";
     print SATOUT "-$v1 0\n"; # then it must have been merged in phase k with a row i < i'
     $clausecount++; # 
  }
}
print OUT "$R1constraints = 0 \n";
print SATOUT "$R1SATconstraints";


# create the inequalities that if row i has been removed by phase k, i.e., TR(i,k) = 1, then there was an R(i,q) or RO(i,q) operation in some phase q < k.
$newTRconstraints = "";
$newTRSATconstraints = "";

print SATOUT "c create the clauses that if row i has been removed by phase k, then there was an R(i,q) or RO(i,q) operation in some phase q < k \n";
foreach $i (1 .. $n) {
   $TRistring = "";
   $TRiSATstring = "";
   foreach $k (1 .. $b) {
      $kp1 = $k + 1;
      $TRistring .= "- R($i,$k) - RO($i,$k) ";
      $v1 = $SATvariable{"R($i,$k)"};
      $v2 = $SATvariable{"RO($i,$k)"};
      $v3 = $SATvariable{"TR($i,$kp1)"};
      $TRiSATstring .= "$v1 $v2 ";
      $newTRconstraints .= "TR($i,$kp1) $TRistring <= 0 \n"; 
      $newTRSATconstraints .= "$TRiSATstring";
      $newTRSATconstraints .= "-$v3 0\n";
      $clausecount++;
   }
}
print OUT "$newTRconstraints \n";
print SATOUT "$newTRSATconstraints";


# create the inequalities that say that in each phase exactly one operation Dr, Dt, Dc, or NOP operation is executed. Further if a NOP operation
# is executed in a phase k, then a NOP operation is executed in phase k+1. This forces all of the real operations to be executed first, followed by
# all NOPs

foreach $k (1 .. $b) {
    $SATvariable{"NOP($k)"} = $SATinteger;
    $SATinteger++;
}

$NOPconstraints = "";
$NOPSATconstraints = "";
foreach $k (1 .. $b) {
   foreach $i (1 .. $n) {
      $NOPconstraints .= "+ R($i,$k) + RO($i,$k) ";
      $v1 = $SATvariable{"R($i,$k)"};
      $v2 = $SATvariable{"RO($i,$k)"};
      $NOPSATconstraints .= "$v1 $v2 ";
   }
   foreach $j (1 .. $m) {
      $NOPconstraints .= "+ C($j,$k) ";
      $v1 = $SATvariable{"C($j,$k)"};
      $NOPSATconstraints .= "$v1 ";
   }
   $NOPconstraints .= "+ NOP($k) = 1 \n"; # exactly one operation is done in each phase k in the ILP formulation.
   $v1 = $SATvariable{"NOP($k)"};
   $NOPSATconstraints .= "$v1 0\n";   # some operation must be done in each phase k, but where do we say that exactly one operation is done in the SAT formulation? Below.
   $clausecount++;

   $kp1 = $k + 1;
   if ($kp1 < $b+1) {
       $NOPconstraints .= "NOP($k) - NOP($kp1) <= 0 \n";
       $bin{"NOP($k)"} = 1;
       $bin{"NOP($kp1)"} = 1;
       $v1 = $SATvariable{"NOP($k)"};
       $v2 = $SATvariable{"NOP($kp1)"};
       $NOPSATconstraints .= "$v2 -$v1 0\n";  # a NOP in phase k implies a NOP in phase k+1
       $clausecount++;
    }
}

print OUT "\n $NOPconstraints";
print SATOUT "$NOPSATconstraints";

# Create the SAT clauses to enforce that only one operation can be done in any phase.  
print SATOUT "c Create the SAT clauses to enforce that only one operation can be done in any phase.\n";

$SATone = "";
foreach $k (1 .. $b) {
         $v5 = $SATvariable{"NOP($k)"};
   foreach $i (1 .. $n) {
         $v1 = $SATvariable{"R($i,$k)"};
         $v4 = $SATvariable{"RO($i,$k)"};
         $SATone .= "-$v1 -$v5 0 \n"; # can't have a NOP and an R op in the same phase
         $SATone .= "-$v4 -$v5 0 \n"; # can't have a NOP and an RO op in the same phase
         $clausecount = $clausecount + 2;
     
     foreach $iprime (1 .. $n) {
         $v2 = $SATvariable{"R($iprime,$k)"};
         $v3 = $SATvariable{"RO($iprime,$k)"};

         if ($i > $iprime) {
             $SATone .= "-$v1 -$v2 0 \n";  # only one R operation can be done in any phase
             $SATone .= "-$v3 -$v4 0 \n";  # only one RO operation can be done in any phase
             $clausecount = $clausecount + 2;
         }

         $SATone .= "-$v1 -$v3 0 \n"; # only one removal operation, R or RO can be done in any phase.  i = i' is allowed here, and this also causes
                                      # about half of the clauses to be redundant, but that is ok.
         $clausecount++;
     }

     foreach $j (1 .. $m) {
         $v2 = $SATvariable{"C($j,$k)"}; 
         $SATone .= "-$v1 -$v2 0 \n"; # only one R or C row or col removal in any phase
         $SATone .= "-$v4 -$v2 0 \n"; # only one RO or C row or col removal in any phase
         $SATone .= "-$v2 -$v5 0 \n"; # can't have a NOP and a C operation in any phase
         $clausecount = $clausecount + 3;

         foreach $jprime (1 .. $j-1) {
              $v6 = $SATvariable{"C($jprime,$k)"};
              $SATone .= "-$v2 -$v6 0 \n";  # only one C operation can be done in any phase
              $clausecount++;
         }
              
     }
   }
}
     
print SATOUT "$SATone \n";

print OUT "binary\n";
foreach $var (sort keys %bin) {
    print OUT "$var \n";
}

print OUT "end";

$SATinteger--;
print "The number of variables is $SATinteger; the number of clauses is $clausecount \n";
print "The output lp file is file $ARGV[1].lp \n";
print "The output SAT file is $ARGV[1].SAT \n";

print SAT_KEY "variable - key correspondence \n"; #DG this block is placed after all the variable and clause generating code.
foreach $key (sort keys %SATvariable) {
        print SAT_KEY "$key, $SATvariable{$key} \n";
}

$tp1 = $target + 1;              # find the integer representing TRO($target + 1, $b + 1)
$bp1 = $b + 1;
$target_integer = $SATvariable{"TRO($tp1,$bp1)"};
print SATOUT  "-$target_integer 0 \n";
$clausecount++;

close (SATOUT);
open (SATOUT, "sat_temp");


print SAT_FINAL "p cnf $SATinteger $clausecount \n";

while ($line = <SATOUT> ) {
   print SAT_FINAL "$line";
}

# DG we should also add the feature of writing out the target clause. Say w is the last phase, and Xi,w denotes that i Dt operations are allowed
# by phase w, then we want a clause that says NOT Xi,w to test if fewer than i Dt operations are possible.

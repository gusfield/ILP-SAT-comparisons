# historybound.pl
#
# DG This program should compute the history bound using the Bafna, Bansal DP in O(m2^n) time for an n by m matrix.   So
# it is slow for large n.
# the input matrix should have no spaces between the bits.
#
# call on a terminal command line as: perl historybound.pl input-file-name
#
# August 22, 2019
#

open (IN, $ARGV[0]);  # Here we read in the 0/1 input matrix, which will be used later.  No spaces between bits.
open (OUT, ">$ARGV[0]history"); # the file where the trace is written

@inarray = <IN>;

#print OUT "@inarray \n";

$bits = @inarray;   # This is the number of lines in inarray, which is also the number of bits in the binary numbers that will be generated, corresponding to
                    # subsets of the lines in inarray

%bin2dec = {}; # hash with binary number index, with decimal value
%sortedones = {}; # hash of number of ones in a binary number, with value equal to a list of all the binary numbers with that
                  # number of ones.

my @binary_list = ();  # list of all of the 2^bits binary strings from 0 to 2^bits - 1.
%oneshash = {};   # hash of binary number index, with value equal to the number of ones in the binary number.
my $remainder;

$allzero = "";
foreach $i (0 ... $bits - 1) {
       $allzero .=  '0';
  }
#print OUT "allzero = $allzero \n";

my $bound = (2**$bits) - 1;
for my $num (0 .. $bound) {
    my $dec_number = $num;
    my $result = "";
    my $onescount = 0;

    my $iters = 0;
    while ($dec_number >= 1)
    {
         $remainder = $dec_number % 2;       #Modulo division to get remainder
         if ($remainder == 1) {
            $onescount++;
         }
         $result = $remainder . $result;     #Concatenation of two numbers
         $dec_number = $dec_number / 2;     #New Value of decimal number to do next set of above operations
         $iters++;
    }

    while ($iters < $bits) {               # fill out the leftmost bits with 0s as needed to get the right
                                       # number of bits
        $result = '0' . $result;
        $iters++;
     }

#print "Num, Binary number, No. of ones  = $num, $result, $onescount \n";

    $last_result = $result;
    push(@binary_list, $result);
    $bin2dec{$result} = $num; # populate hash bin2dec with binary index and decimal value
    $oneshash{$result} = $onescount;
    if (! defined $sortedones{$onescount}) { 
        $sortedones{$onescount} = [$result];
    }
    else {
        push (@{$sortedones{$onescount}}, $result);
    }
}

#print "@binary_list \n";

%history_bound = (); # hash for the history_bound values of subsets of rows, indexed by the binary vector specifying the subset.
$history_bound{$allzero} = 0; # the history bound for the empty subset is 0. It is also 0 for any singleton, but we have not implemented
                              # that.

foreach $onescount (0 .. $bits) {  # order by the number of ones in the binary number
     foreach $result (@{$sortedones{$onescount}}) { # for each binary number with onescount number of ones
#             print OUT "$result, $onescount \n";


# Next we want to use the binary number (result) to select a set of rows of an input matrix, creating a new matrix that we can send
# to clean.

             @subset = ();
             @result_bits = split (//,$result);
             foreach $i (0 .. $bits -1) {
#                     print OUT "$result_bits[$i]\n";
                     if ($result_bits[$i] == 1) {
#                         chomp $inarray[$i];
#                         print OUT "Q $i, $inarray[$i] \n";
                         push (@subset, $inarray[$i]);  # subset collects the row in the input matrix specified by the binary number in result.
#                         print OUT "subset in main, while being constructed: \n @subset \n";
                     }
              }

              foreach $row (@subset) {
#                   print OUT "W $row \n";
              }

    $subsetlen = @subset;
#    print OUT "subset length = $subsetlen\n";

    @cleanarray = ();
#    print "About to call clarray \n";
#    @cleanedarray = clarray ($result, @subset);  # pass both the binary vector detailing the indexes of the subset, and then the subset itself.
    ($newresult, @cleanedarray) = clarray ($result, @subset);  # pass both the binary vector detailing the indexes of the subset, and then the subset itself.
                                                               # newresult is the binary vector detailing the rows of the cleaned array.
#    print OUT "The cleaned array after return from clarray \n"; 
#    print "The cleaned array after return from clarray \n";

#    print OUT "The binary result vector after return from clarray: $newresult \n";
#    print "The result vector after return from clarray: $newresult \n";
    foreach $line (@cleanedarray) {
#         print OUT "$line \n";
#         print "$line \n";
    }

#   print OUT "\n";


# Here we implement the crux of the history bound DP computation. For each row in the cleaned array, remove the row, create the new binary number reflecting
# the remaining subset of rows, look up the history-bound for the remaining matrix, then add one. Minimizing over all of these options, record the
# value in the hash history-bound, indexed by the binary result vector.

  print OUT "The subset of rows of the input specified by $result cleans to subset $newresult \n";
  if (defined $history_bound{$newresult}) { 
     $history_bound{$result} = $history_bound{$newresult};
     print OUT "The subset $newresult of $result has been seen before \n";
     print OUT "history bound = $history_bound{$result} \n";
  }
  else {
     @newresult_bits = split(//, $newresult); 
     $best_bound = 100000;

     foreach $bit (0 ... $bits-1) {
        if ($newresult_bits[$bit] == 1) {  # if there is a 1 at position bit, then change it to 0 in bindex, which implements the act of removing that row.
          @bindex = @newresult_bits;
          $bindex[$bit] = 0;
          $index = join('',@bindex);
          $sub_history_bound = 1 + $history_bound{$index}; # add 1 (for the row removal) to the history_bound computed for the subset specified by index.
          if ($sub_history_bound < $best_bound) {
                $best_bound = $sub_history_bound;
                $best_sub = $index;
                print OUT "Y best bound = $best_bound \n";
                print OUT "Z Best sub = $best_sub \n";
          }
         }
       } # end of foreach bit. At this point the history bound for the subset specified by result should be equal to the value of best_bound.
    $history_bound{$result} = $best_bound;
    }
   print OUT "X $result: history bound = $history_bound{$result} \n\n";

#   print "X $result: history bound = $history_bound{$result} \n\n";

  } # end of foreach result in sortedones
 print OUT "\n";
} # end of foreach onescount

   print OUT "history bound of $last_result = $history_bound{$last_result} \n";
   print "history bound of $last_result = $history_bound{$last_result} \n";
   print "A trace of the computation is in file: $ARGV[0]history \n";

############
sub clarray {  # cleanarray calls cleaniter repeatedly until no changes are made in an iteration

%rowhash = ();
my $row = 0;

@cinarray = @_; 
# print "cinarray before shift: \n @cinarray \n";

$cbinary= shift @cinarray;
#print OUT "In clarray, the string cbinary is $cbinary\n";  # cbinary is a binary string of length = bits, detailing the subset of rows in cinarray.
#print "In clarray, the string cbinary is $cbinary\n";  # cbinary is a binary string of length = bits, detailing the subset of rows in cinarray.
#print "cinarray after shift: @cinarray \n";

foreach $line (@cinarray) {
       chomp $line;
#       print OUT "In clarray: $line \n";
       $rowhash{$row} = $line;
       $row++;
}

my $line_count = $row;   # a true count of the number of rows. But the largest index for the rows is $row-1.
my $line_length = length $cinarray[0];
#print OUT "Here is where line_length is assigned: $line_length \n";

my $old_line_count = 100000; # start with a large number bigger than the actual number of rows.
my $old_line_length = 1000000;

foreach $row (sort {$a <=> $b} keys %rowhash)  {  # what is this really for?
#   print OUT "$rowhash{$row} : $row \n";
 #  push (@cinarray, $rowhash{$row});
}


while (($line_count < $old_line_count) or ($line_length < $old_line_length))  {  # while we continue to make changes in the array, either removing a row
                                                                                 # or removing a column.
    $old_line_count  = $line_count;  # update the count and length
    $old_line_length = $line_length;

    @ccleanarray = ();
#    print OUT "About to call cleaniter with binary string $cbinary\n";

    ($newcbinary, @ccleanarray) = cleaniter ($cbinary,@cinarray);

    if (! $ccleanarray[0]) {  # if ccleanarray is empty, set the count and length to 0
        $line_count = $line_length = 0;
    }

    else {
         $line_count = @ccleanarray; # update line_count with the new number of rows
         $line_length = length($ccleanarray[0]);  # update the new line length
    }


    $cbinary = $newcbinary;
    @cinarray = @ccleanarray;
#    $cinarray_len = @cinarray;
#     print OUT "cbinary; old_line_count, line_count, old_line_length, line_length: $cbinary; $old_line_count, $line_count, $old_line_length, $line_length \n";
#     print "at the end of the while statement - returning to the top \n";
#     print OUT "at the end of the while statement in clarray - returning to the top to compare old values with new values \n";
}  # end of while statement

#    print OUT "\n The cleaned array has $line_count lines, each with $line_length bits\n";
    foreach $line (@ccleanarray) {
#        print OUT "H $line \n";  
    }

# print OUT "The number of rows in the cleaned array is $cinarray_len \n";

return ($cbinary, @cinarray);
}
################

sub cleaniter {
# remove duplicate rows and uninformative columns.
#print OUT "entering cleaniter \n";

my ($cbinary, @inlines) = @_;
#print OUT "Inside cleaniter. cbinary is $cbinary \n";
@cbinarybits = split (//,$cbinary);
%insequence = ();
@lines = ();
@outlines = ();

$j = 0;
foreach $line (@inlines) {  # this block will remove duplicate rows in the input sequences
   chomp $line;
   while ($cbinarybits[$j] eq 0) { # find the next 1 in cbinarybits. The way that j and inlines are coordinated, there always should be
                                   # a next 1 at this point.
#        print "$j \n";
        $j++;
   }
      
#   print OUT "$j, $cbinarybits[$j]: $line \n";
   if (!defined $insequence{$line}) {
      $insequence{$line} = 1;
      push (@lines, $line);
   }
   else {
        $cbinarybits[$j] = 0; # if the line is a duplicate, don't add it to @lines, and change bit j to 0 in cbinarybits
#        print OUT "cbinarybits when line $j is a duplicate @cbinarybits \n";
   }
   $j++;
}

$cbinary = join ('', @cbinarybits);
# print OUT "The new cbinary in cleaniter, after removing duplicate rows, is $cbinary \n";

# Having removed duplicate rows, we now remove uninformative columns. But it is easier to work with rows, so we first transpose the matrix.

@tlines = transpose(@lines);  # transpose the matrix @lines
@translines = ();
$num_goodlines = 0;

foreach $line (@tlines) {   # examine each row (which was originally a col.) to see if it has
                            # more than one entry of value 1, and at least one 0. If so, then add that row to the growing @translines.

      @bits = split (//,$line);
      $line_length = @bits;
      $onecount = 0;
      foreach $bit (@bits) {
         if ($bit == 1) {
            $onecount++;
         }
#      print OUT "bit and onecount: $bit $onecount \n";
      }

      if ($onecount > 1) {
#      if (($onecount > 1) and ($onecount < $line_length)) { # don't accumulate a line (actually a column in the inlines array) if it only has a single 1 or
                                                            # it has all ones. These cases are not informative. Note the asymmetry because we are
                                                            # assuming that the root sequence is the all-zero sequence. So, we will accumulate a line
                                                            # that has only a single 0.
#         print "XXX @bits \n";
         $goodline = join ('',@bits);
#         print OUT "goodline: $goodline \n";
         $num_goodlines++;
         push (@translines, $goodline);
      } 
#print "\n";
}

#print OUT "The number of goodlines is $num_goodlines \n";
#print OUT "In cleaniter translines:  \n";
foreach $lIne (@translines) {
   # print  OUT "$lIne \n";
}

if ($num_goodlines == 0) {   # create and return cbinary as the all-zero string.
  $len_cbinary = length $cbinary;
  $cbinary = "";
  foreach $i (0 ... $len_cbinary - 1) {
       $cbinary .=  '0';
  }
}
else {
    @outlines = transpose(@translines);
}

#print OUT "About to exit cleaniter. The returned cbinary is $cbinary \n";
#print OUT "The resulting outlines matrix is \n ";
foreach $outlin (@outlines) {
#      print OUT "$outlin \n";
}

$num_lines_in_outlines = @outlines;
#print OUT "The number of lines in outlines is $num_lines_in_outlines \n";

return ($cbinary, @outlines);
}


#####################
sub transpose {

@lines = @_;

@transpose = ();
$i = 0;
foreach $line (@lines) {
  chomp $line;
  @row = split(//,$line);
  foreach $j (0 ... length($line) - 1) {
     $transpose[$j][$i] = $row[$j];
#     print "$i, $j, $row[$j], $transpose[$j][$i]\n";
  }
# print "\n";
$i = $i + 1;
$linelength = length($line);
}

# print "The number of rows in the transpose is $linelength, and the number of cols. is $i \n";

 @trans = ();
 foreach $p (0 ... $linelength - 1) {
    $newrow = "";
    foreach $q (0 ... $i-1) {
#      print "$transpose[$p][$q]";
      $newrow = $newrow . $transpose[$p][$q];
    }
#    print "\n";
    push (@trans, $newrow);
 }

# print "XXXXXX\n";
# foreach $line (sort @trans) {
#      print CRES "$line\n";
# }

return @trans;
}

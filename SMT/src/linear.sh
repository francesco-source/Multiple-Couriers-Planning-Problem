#!/bin/bash
file=$1
o_variable=$2
o_value=$3
l_bound=$4
couriers=$6
packages=$7
solver_choice=$5


if [[ "$solver_choice" == "cvc4" ]]; then
    solver=( cvc4 --lang smt --produce-models --incremental )
else
    echo "SOLVER NOT SUPPORTED" >&2
    exit 1
fi

assert_statement="(assert (< $o_variable $o_value))"
check_sat="(check-sat)"
get_value="(get-value ($o_variable))"


{
  echo "$assert_statement" 
  echo "$check_sat" 
  echo "$get_value" 
} >> "$file"

unsat=0
o_value=$((o_value - 1))
one_sat=0
while true;
do
  first=0
  while read text;
  do
    if [ "$text" == 'unsat' ]; then
      unsat=1
      break;
    fi

    one_sat=1


    if [[ $first -eq 0 ]];then 
      sed -i '$ d' $file
      sed -i '$ d' $file

      # add assertions
      assert_statement="(assert (< $o_variable $o_value))"
      check_sat="(check-sat)"
      get_value="(get-value ($o_variable))"

      {
        echo "$assert_statement"
        echo "$check_sat"
        echo "$get_value"
      } >> "$file"

      first=1

    else 

      # get current solution
      val=$(echo "$text" | sed 's/[^0-9]*//g') 

      if [ $o_value -gt $val ]; then
        o_value=$val #update objective value
      else
        o_value=$((o_value - 1)) #search for a better solution
      fi
    fi 
done < <("${solver[@]}" <"$file")
if [ $unsat = 1 ]; then
    break;
fi
done


if [[ $one_sat -eq 0 ]] then #if no solution has been found
  if [ "$text" == 'unsat' ]; then
    echo '======= UNSAT ======'
  else
    echo '===== UNKNOWN ====='
  fi

elif [ "$text" == 'unsat' ]; then #if unsat the previous is the optimal solution
  echo $val
  sed -i '$ d' $file 
  sed -i '$ d' $file 
  sed -i '$ d' $file 
  
  for ((i=0; i<couriers; i++));do
  for ((j=0; j<packages; j++));do

      declare_fun="(declare-fun path${i}_${j} () Int)"
      assert_equal="(assert (= (select asg${i} ${j}) path${i}_${j}))"
      {
        echo "$declare_fun"
        echo "$assert_equal"
      } >> "$file"

  done
  done

  echo "(check-sat)" >> $file

  for ((i=0; i<couriers; i++));do
  for ((j=0; j<packages; j++));do

    echo "(get-value (path$i"_"$j))">> $file
  
  done
  done
  
  while read text; do
  	if [ "$text" != 'sat' ]; then
  	   	echo $text
  	fi
  done < <("${solver[@]}" <"$file") 
  
fi

rm pkill sleep 2>/dev/null


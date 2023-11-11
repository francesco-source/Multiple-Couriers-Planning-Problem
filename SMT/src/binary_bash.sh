solver_choice=$1
#check if the solver is correct
if [[ "$solver_choice " == "cvc4"]] then;
    solver=( cvc4 --lang smt --produce-models --incremental )
fi
else
    echo "SOLVER NOT SUPPORTED" >&2
    exit 1
fi

file=$2
couriers=$3
packages=$4
o_variable=$5
o_value=$6
u_bound= $o_value
l_bound=$7

{
  cat <<EOF
(assert (>= $o_variable $lw_bound))
(assert (<= $o_variable $o_value))
(check-sat)
(get-value ($o_variable))
EOF
} >> "$file"

bound_difference=$((up_bound - lw_bound))
distance=$((bound_difference / 2))
middle=$((u_bound - distance))

$one_sat = 0
$sat = 0 
$unsat = 0 
$new_sol=0 
$first = 0
while true;
do 
    first=0
    while read text;
    do
    : '
     if the solution is unsat and not other 
     feasible solution has been found -> exit

    '
     if [[ $one_sat == 0 && "$text" -eq "unsat"]]; then
        break
     fi
     one_sat=1

     case $text in
        sat)   $sat=1;;
        unsat) $unsat=1;;
        
        esac

     if [ "$bound_difference" -eq 1 ]; then
        middle=$l_bound
     
     else
      middle=$((up_bound - distance))
     fi

     if [ "$distance" -lt 1 ] then;
        break;
     fi

     # the line read is sat or unsat
    if [ "$unsat" -eq 1 ];then
        if [ $first = 0 ];then
   	    sed -i '$ d' $file  
        sed -i '$ d' $file
        sed -i '$ d' $file
        else
        val=$(echo "$line" | sed 's/[^0-9]*//g') 
        o_value=$val
        u_bound=$o_value
        distance=$((bound_difference / 2))
        middle=$((u_bound - distance))
        bound_difference=$((up_bound - lw_bound))

        fi
   
    else
        if [ $first = 0 ];then
        sed -i '$ d' $file
        sed -i '$ d' $file
        else
        l_bound=$middle
        
        distance=$((bound_difference / 2))
        middle=$((u_bound - distance))
        bound_difference=$((up_bound - lw_bound))
        fi

         {
  cat <<EOF
(assert (<= $o_variable $o_value))
(check-sat)
(get-value ($o_variable))
EOF
} >> "$file"
             

    fi




    done <("${solver[@]}" <"$file")
    if [[ "$distance" -lt 1  || ($one_sat == 0 && "$text" -eq "unsat") ]]; then
    break;
    fi


done 


if [[ "$text" -eq "sat" ]]; then
    sed -i '$ d' $file 
    sed -i '$ d' $file 
    sed -i '$ d' $file 

    echo $o_value
    for ((i=0; i<couriers; i++));do
    for ((j=0; j<items; j++));do
{
  cat <<EOF
"(declare-fun path$i"_"$j () Int)"        
"(assert (= (select asg$i $j) path$i"_"$j))
EOF
} >> "$file"
        
        
    done
    done

    echo "(check-sat)" >> $in_file


    for ((i=0; i<couriers; i++));do
        for ((j=0; j<packages; j++));do
        echo "(get-value (path$i"_"$j))">> $file
        done
    done
rm pkill sleep 2>/dev/null




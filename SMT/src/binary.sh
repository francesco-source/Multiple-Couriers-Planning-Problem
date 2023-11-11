solver_choice=$5
#check if the solver is correct
if [[ "$solver_choice" == "cvc4" ]]; then
    solver=( cvc4 --lang smt --produce-models --incremental )
else
    echo "SOLVER NOT SUPPORTED" >&2
    exit 1
fi


file=$1
couriers=$6
packages=$7
o_variable=$2
o_value=$3
l_bound=$4

o_variable_lower_bound="(assert (>= $o_variable $l_bound))"
o_variable_upper_bound="(assert (<= $o_variable $o_value))"
check_sat="(check-sat)"
get_value="(get-value ($o_variable))"

{
    echo "$o_variable_lower_bound"
    echo "$o_variable_upper_bound" 
    echo "$check_sat"
    echo "$get_value" 
} >> "$file"

u_bound=$o_value
bound_difference=$((u_bound - l_bound))
distance=$((bound_difference / 2))
middle=$((u_bound - distance))

one_sat=0
sat=1
unsat=0 

while true;
do 
    first=0
    while read text;
    do
    : '
     if the solution is unsat and not other 
     feasible solution has been found -> exit

    '

     if [[ $one_sat = 0 && "$text" = 'unsat' ]]; then
        unsat=1 
        break
    fi


     one_sat=1
     case $text in
        sat)   sat=1;;
        unsat) sat=0;;
        esac

     if [ "$bound_difference" -eq 1 ]; then
        middle=$l_bound
     else
      middle=$((u_bound - distance))
     fi

     if [ "$distance" -lt 1 ]; then
        unsat=1
     fi



    if [[ $first -eq 1 ]]; then
        if [[ $sat -eq 1 ]]; then
            o_value=$(echo "$text" | sed 's/[^0-9]*//g')
            u_bound=$o_value
            bound_difference=$((u_bound - l_bound))
            distance=$((bound_difference / 2))
            middle=$((u_bound - distance))
        else
            l_bound=$middle
            bound_difference=$((u_bound - l_bound))
            distance=$((bound_difference / 2))
            middle=$((u_bound - distance))
            fi

            assert_statement="(assert (<= $o_variable $middle))"
            check_sat="(check-sat)"
            get_value="(get-value ($o_variable))"

            {
                echo "$assert_statement" 
                echo "$check_sat" 
                echo "$get_value" 
            } >> "$file"
            
  else
   first=1

        if [[ $sat -eq 0 ]]; then
            sed -i '$ d' $file
        fi
        sed -i '$ d' $file
        sed -i '$ d' $file

  fi

 done < <("${solver[@]}" <"$file")

   if [ $unsat = 1 ]; then
    break;
    fi

done 


   

if [[ $one_sat -eq 1 ]]; then
    sed -i '$ d' $file 
    sed -i '$ d' $file 
    sed -i '$ d' $file 
    echo $o_value
    for ((i=0; i<couriers; i++)); do
    for ((j=0; j<packages; j++)); do
          declare_fun="(declare-fun path${i}_${j} () Int)"
          assert_equal="(assert (= (select asg${i} ${j}) path${i}_${j}))"

            {
                echo "$declare_fun" 
                echo "$assert_equal" 
            } >> "$file"
           done 
    done
    echo "(check-sat)" >> $file

    for ((i=0; i<couriers; i++)); do
    for ((j=0; j<packages; j++)); do
        echo "(get-value (path$i"_"$j))">> $file
    done
    done
     while read text; do
  	if [[ $text != 'sat' ]]; then
	    echo $text  
  	fi
  
    done < <("${solver[@]}" <"$file")
else
    if [ "$text" == 'unsat' ]; then
    echo '======== UNSAT ======='
  else
    echo '====== UNKNOWN ======='
  fi


fi


        
  

rm pkill sleep 2>/dev/null
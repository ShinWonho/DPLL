#!/bin/bash

for folder in `ls "test"`; do
	for expected_result in `ls "test/$folder"`; do
		echo -ne "$folder/$expected_result runs...\r"
		startTime=$((`date +%s`*1000+`date +%-N`/1000000))
		tests=0
		success=0
		for file in `ls "test/$folder/$expected_result"`; do
			tests=$(($tests+1))
			actual_result=$(python3 solvepy3.py "test/$folder/$expected_result/$file")
			if [[ $actual_result = $expected_result ]] ; then
				success=$(($success+1))
			else
				echo "[Failed] $folder/$expected_result/$file expected:$expected_result actual: $actual_result"
			fi
			endTime=$((`date +%s`*1000+`date +%-N`/1000000))
			echo -ne "$folder/$expected_result [$tests/$success] (avg $(((endTime - startTime)/tests))ms)...\r"
		done
		if [[ $tests -ne 0 ]] ; then
			endTime=$((`date +%s`*1000+`date +%-N`/1000000))
			echo "$folder/$expected_result [$tests/$success] (avg $(((endTime - startTime)/tests))ms)             "
		fi
	done
done

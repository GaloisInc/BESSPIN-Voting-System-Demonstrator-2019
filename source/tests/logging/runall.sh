#!/bin/bash
./test1 >test_results/test1.out
mv test1log.txt test_results

./test2 >test_results/test2.out
mv test2log.txt test_results

./test3 >test_results/test3.out
mv test3log.txt test_results

./test4 >test_results/test4.out
mv test4log.txt test_results

./test5 >test_results/test5.out
mv test5log.txt test_results

./test6 >test_results/test6.out
mv test61log.txt test_results
mv test62log.txt test_results

./test7 >test_results/test7.out
mv test7*.txt test_results

./test8 >test_results/test8.out
mv test8log.txt test_results

./test9 test_data/good1.txt >test_results/test9.out 2>&1
./test9 test_data/good2.txt >>test_results/test9.out 2>&1
./test9 test_data/good3.txt >>test_results/test9.out 2>&1
./test9 test_data/goodmany.txt >>test_results/test9.out 2>&1
./test9 test_data/bad1data.txt >>test_results/test9.out 2>&1
./test9 test_data/bad1mac.txt >>test_results/test9.out 2>&1
./test9 test_data/bad3data2.txt >>test_results/test9.out 2>&1
./test9 test_data/bad3data3.txt >>test_results/test9.out 2>&1
./test9 test_data/bad3hash2.txt >>test_results/test9.out 2>&1
./test9 test_data/bad3hash3.txt >>test_results/test9.out 2>&1
./test9 test_data/missing_first_block.txt >>test_results/test9.out 2>&1
./test9 test_data/missing_middle_block.txt >>test_results/test9.out 2>&1
./test9 test_data/junk1.txt >>test_results/test9.out 2>&1

./test10 test_data/good1.txt >test_results/test10.out 2>&1
./test10 test_data/good2.txt >>test_results/test10.out 2>&1
./test10 test_data/good3.txt >>test_results/test10.out 2>&1
./test10 test_data/goodmany.txt >>test_results/test10.out 2>&1
./test10 test_data/bad1data.txt >>test_results/test10.out 2>&1
./test10 test_data/bad1mac.txt >>test_results/test10.out 2>&1
./test10 test_data/bad3data2.txt >>test_results/test10.out 2>&1
./test10 test_data/bad3data3.txt >>test_results/test10.out 2>&1
./test10 test_data/bad3hash2.txt >>test_results/test10.out 2>&1
./test10 test_data/bad3hash3.txt >>test_results/test10.out 2>&1
./test10 test_data/missing_first_block.txt >>test_results/test10.out 2>&1
./test10 test_data/missing_middle_block.txt >>test_results/test10.out 2>&1
./test10 test_data/junk1.txt >>test_results/test10.out 2>&1

./testimport test_data/good1.txt >test_results/testimport.out 2>&1
./testimport test_data/good2.txt >>test_results/testimport.out 2>&1
./testimport test_data/good3.txt >>test_results/testimport.out 2>&1
./testimport test_data/goodmany.txt >>test_results/testimport.out 2>&1
./testimport test_data/bad1data.txt >>test_results/testimport.out 2>&1
./testimport test_data/bad1mac.txt >>test_results/testimport.out 2>&1
./testimport test_data/bad3data2.txt >>test_results/testimport.out 2>&1
./testimport test_data/bad3data3.txt >>test_results/testimport.out 2>&1
./testimport test_data/bad3hash2.txt >>test_results/testimport.out 2>&1
./testimport test_data/bad3hash3.txt >>test_results/testimport.out 2>&1
./testimport test_data/missing_first_block.txt >>test_results/testimport.out 2>&1
./testimport test_data/missing_middle_block.txt >>test_results/testimport.out 2>&1
./testimport test_data/junk1.txt >>test_results/testimport.out 2>&1
mv test_data/*.txt test_results
cd test_data
git checkout -- .
cd ..

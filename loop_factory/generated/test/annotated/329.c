int main1(int k){
  int ecyw, j56;
  ecyw=(k%40)+19;
  j56=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ecyw == (\at(k, Pre) % 40) + 19;
  loop invariant j56 >= 0;
  loop invariant k >= \at(k, Pre);
  loop assigns j56, k;
*/
while (j56!=j56) {
      j56 = j56;
      j56 = (j56+ecyw/j56)/2;
      k = k + j56;
  }
}
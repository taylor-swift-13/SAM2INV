int main1(int a){
  int j, k, f;

  j=25;
  k=0;
  f=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant j == 25;
  loop invariant 0 <= k;
  loop invariant k <= j;
  loop invariant 0 <= k <= j;
  loop invariant k >= 0;
  loop assigns k;
*/
while (k<j) {
      k = k+1;
  }

}

int main1(int a,int b){
  int n, j, v;

  n=17;
  j=0;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - (n+6)*j == 5;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n == 17;
  loop invariant j >= 0;
  loop invariant v == 5 + 23 * j;
  loop invariant v == 5 + j*(n+6);
  loop assigns v, j;
*/
while (1) {
      v = v+n;
      v = v+6;
      j = j+1;
  }

}

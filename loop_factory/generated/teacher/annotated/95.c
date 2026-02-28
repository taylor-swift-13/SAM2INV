int main1(int b,int m){
  int o, n, v, j;

  o=8;
  n=o;
  v=-4;
  j=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;
  loop invariant v == -4;
  loop invariant n % 4 == 0;
  loop invariant (0 <= n) && (n <= 8);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant o == 8;
  loop invariant n >= 0;
  loop invariant n <= 8;
  loop invariant n <= o;
  loop assigns v, n;
*/
while (n>3) {
      v = v+j+j;
      n = n-4;
  }

}

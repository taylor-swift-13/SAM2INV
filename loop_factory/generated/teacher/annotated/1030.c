int main1(int b,int m){
  int n, d, j;

  n=(b%37)+5;
  d=0;
  j=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(b, Pre) % 37 + 5;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);

  loop invariant n == (\at(b, Pre) % 37) + 5;



  loop invariant b == \at(b, Pre) && m == \at(m, Pre);

  loop invariant (j - \at(m, Pre)) % 2 == 0;
  loop invariant -31 <= n && n <= 41;

  loop assigns j;
*/
while (1) {
      j = j+4;
      if (j+1<n) {
          j = j%6;
      }
  }

}

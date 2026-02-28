int main1(int b,int m,int n,int p){
  int r, x, s, k;

  r=52;
  x=0;
  s=m;
  k=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x <= r/2;
  loop invariant k % 2 == 0;
  loop invariant (s - \at(m, Pre)) % 2 == 0;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant x == 0;
  loop invariant r == 52;


  loop invariant x < r/2;

  loop assigns s, k;
*/
while (1) {
      if (x<r/2) {
          s = s+k;
      }
      else {
          s = s+1;
      }
      s = s+2;
      k = k+s;
      k = k+k;
      s = s+x;
  }

}

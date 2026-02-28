int main1(int a,int b,int m,int n){
  int z, s, v, q, w, x;

  z=(b%14)+14;
  s=0;
  v=n;
  q=-6;
  w=4;
  x=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant v >= \at(n,Pre);
  loop invariant q <= w;
  loop invariant w == 4;
  loop invariant q == -6;
  loop invariant v >= (\at(n, Pre));
  loop invariant z == (b % 14) + 14;
  loop invariant v >= n;
  loop invariant z == ((\at(b,Pre) % 14) + 14);
  loop assigns q, v;
*/
while (1) {
      if (w<=q) {
          q = w;
      }
      v = v+1;
  }

}

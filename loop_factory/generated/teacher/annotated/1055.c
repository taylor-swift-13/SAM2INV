int main1(int n,int p){
  int u, x, v;

  u=(n%31)+20;
  x=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == \at(n, Pre) % 31 + 20;
  loop invariant x == 0;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v + 5) % 2 == 0;
  loop invariant v >= -5;
  loop invariant u == (\at(n, Pre) % 31) + 20;
  loop invariant u == (n % 31) + 20;
  loop invariant n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant u == (\at(n, Pre) % 31 + 20);
  loop invariant x % 8 == 0;

  loop invariant x == 0 && u == \at(n, Pre) % 31 + 20 && p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant (v + 5) % 2 == 0 && v >= -5 && (x % 8) == 0;

  loop invariant u == n % 31 + 20;
  loop assigns v;
*/
while (1) {
      v = v+2;
      if ((x%8)==0) {
          v = v+x;
      }
  }

}

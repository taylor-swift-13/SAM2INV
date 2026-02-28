int main1(int n,int p){
  int x, u, w;

  x=65;
  u=x;
  w=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 65;
  loop invariant x == 65;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (u+2 <= n+x) ==> ((w - \at(p, Pre)) % 8 == 0);
  loop invariant (u+2 > n+x) ==> ((w - \at(p, Pre)) % 3 == 0);
  loop invariant u == x;
  loop invariant w >= \at(p, Pre);
  loop invariant u >= 0;
  loop invariant u <= 65;
  loop invariant (n >= 2) ==> ((w - \at(p, Pre)) % 8 == 0);
  loop assigns w;
*/
while (u>0) {
      w = w+3;
      if (u+2<=n+x) {
          w = w+5;
      }
  }

}

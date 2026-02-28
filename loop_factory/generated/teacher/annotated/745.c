int main1(int b,int k,int m,int q){
  int n, x, v, w, u, o, a, h;

  n=m;
  x=0;
  v=b;
  w=x;
  u=q;
  o=m;
  a=-4;
  h=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (n == m);
  loop invariant ( (v - \at(b,Pre)) % 8 == 0 );
  loop invariant ( w == 0 || w == u );
  loop invariant v >= b;
  loop invariant (v - b) % 8 == 0;
  loop invariant n == m;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v >= \at(b, Pre);
  loop invariant w == 0 || w == u;
  loop assigns v, w;
*/
while (1) {
      v = v+3;
      if (u<=w) {
          w = u;
      }
      v = v+5;
  }

}

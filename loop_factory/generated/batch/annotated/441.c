int main1(int n,int q){
  int h, j, v, g;

  h=q+20;
  j=2;
  v=n;
  g=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == q + 20;
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= n;
  loop invariant (v - n) % 2 == 0;
  loop invariant ((g == -8 && v == \at(n, Pre)) || (g == 2*v - 4));
  loop invariant ((v == n) && (g == -8)) || (g == 2*(v - 2));
  loop invariant (g == -8) || (g == 2*(v - 2));
  loop invariant h == \at(q, Pre) + 20;
  loop invariant v >= \at(n,Pre);
  loop invariant (v - \at(n,Pre)) % 2 == 0;
  loop assigns g, v;
*/
while (1) {
      g = v;
      v = v+2;
      g = g+g;
  }

}

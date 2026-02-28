int main1(int n,int p,int q){
  int h, j, v, g;

  h=19;
  j=0;
  v=0;
  g=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant v <= h;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant h == 19;
  loop invariant 0 <= v <= h;
  loop invariant g >= q;
  loop invariant g >= q + v*(v+1)/2;
  loop invariant 0 <= v;
  loop invariant n == \at(n, Pre);
  loop invariant (v <= 9) ==> g == q + v*(v+1)/2;
  loop assigns g, v;
*/
while (v<h) {
      if (v>=h/2) {
          g = g+4;
      }
      v = v+1;
      g = g+v;
  }

}

int main1(int u,int c){
  int sl, y2i, at, xi, hwu, oc7;
  sl=u+25;
  y2i=0;
  at=0;
  xi=0;
  hwu=y2i;
  oc7=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sl == u + 25;
  loop invariant y2i == 0;
  loop invariant 0 <= xi;
  loop invariant hwu == sl * xi;
  loop invariant at == u * xi;
  loop assigns xi, hwu, at;
*/
while (xi<=sl-1) {
      xi = xi + 1;
      hwu = hwu+sl-y2i;
      at = at + u;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oc7 <= xi;
  loop invariant c == \at(c, Pre);
  loop invariant oc7 >= u;
  loop assigns hwu, c, oc7;
*/
while (1) {
      if (!(oc7<xi)) {
          break;
      }
      hwu = hwu + u;
      c += y2i;
      oc7++;
  }
}
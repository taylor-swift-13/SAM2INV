int main1(int g){
  int id, cr6, u, xax, u817;
  id=25;
  cr6=2;
  u=0;
  xax=0;
  u817=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g, Pre) + 21*(xax/7) + ((xax%7)*((xax%7)+1))/2;
  loop invariant u817 == xax;
  loop invariant 0 <= xax <= id;
  loop invariant g >= \at(g,Pre);
  loop invariant xax <= id;
  loop invariant 0 <= xax;
  loop assigns g, u, u817, xax;
*/
while (xax<id) {
      u = u + g;
      u817++;
      xax++;
      g = g+(xax%7);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g, Pre) + 21*(xax/7) + ((xax%7)*((xax%7)+1))/2;
  loop invariant 0 <= xax - id;
  loop invariant id <= xax;
  loop assigns cr6, id, u817;
*/
while (id<xax) {
      u817 = u817 + g;
      id++;
      cr6 = cr6 + u817;
      cr6 = cr6*2;
  }
}
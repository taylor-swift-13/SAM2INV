int main1(int a,int q){
  int g, r, u, w;

  g=51;
  r=0;
  u=g;
  w=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 51;
  loop invariant 0 <= r <= g;
  loop invariant 0 <= u <= 51;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= r && r <= g && ((r == 0) ==> (u == g)) && ((r > 0) ==> (u == 0));
  loop invariant (r == 0) ==> (u == g);
  loop invariant (r > 0) ==> (u == 0);
  loop invariant r <= g;
  loop invariant 0 <= u;
  loop invariant u <= g;
  loop invariant u >= 0;
  loop assigns r, u;
*/
while (r<g) {
      u = u*u+u;
      u = u%4;
      r = r+1;
  }

}

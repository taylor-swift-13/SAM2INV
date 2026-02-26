int main1(int a,int q){
  int g, r, u, w;

  g=51;
  r=0;
  u=g;
  w=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g == 51;
  loop invariant u <= 2*g + 1;
  loop invariant u >= g;
  loop invariant u >= 0;
  loop assigns u;
*/
while (u<g) {
      if (u<g) {
          u = u+1;
      }
      u = u*2+1;
  }

}

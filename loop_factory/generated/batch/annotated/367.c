int main1(int a,int q){
  int g, r, u, w;

  g=51;
  r=0;
  u=g;
  w=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 51 && 51 <= u && u <= g && (\at(q, Pre) == 0 ==> w == 0);
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant u <= g;
  loop invariant g == 51;
  loop invariant 51 <= u;
  loop invariant u == g;
  loop invariant w == \at(q, Pre);
  loop assigns u, w;
*/
while (u<g) {
      if (u<g) {
          u = u+1;
      }
      w = w+w;
  }

}

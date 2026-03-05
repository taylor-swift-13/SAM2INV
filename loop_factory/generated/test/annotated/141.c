int main1(int g){
  int gm4, u, i, jt;
  gm4=64;
  u=3;
  i=0;
  jt=17;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jt + i == 17;
  loop invariant u <= gm4;
  loop invariant g == \at(g, Pre) + (((4 + u) * (u - 3)) / 2);
  loop invariant i == ((u - 3) % 2);
  loop invariant 3 <= u;
  loop assigns g, i, jt, u;
*/
while (u<gm4) {
      if (i==0) {
          i = i + 1;
          jt--;
          i = 1;
      }
      else {
          i--;
          jt = jt + 1;
          i = 0;
      }
      u = u + 1;
      g = g + u;
  }
}
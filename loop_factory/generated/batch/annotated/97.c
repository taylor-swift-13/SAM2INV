int main1(int b){
  int g, u, s;

  g=33;
  u=0;
  s=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u;
  loop invariant u <= g;
  loop invariant s == -2 + u*(u-1)/2;
  loop invariant b == \at(b, Pre);
  loop invariant s == u*(u - 1)/2 - 2;
  loop invariant s == -2 + (u*(u-1))/2;
  loop invariant g == 33;
  loop invariant 2*(s + 2) == u*(u - 1);
  loop assigns s, u;
*/
while (u<g) {
      s = s+u;
      u = u+1;
  }

}

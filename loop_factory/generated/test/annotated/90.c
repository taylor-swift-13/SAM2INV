int main1(){
  int d, c, u;
  d=1+17;
  c=0;
  u=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 18;
  loop invariant c <= d;
  loop invariant u == 3*c + 4;
  loop invariant 0 <= c;
  loop assigns c, u;
*/
while (c<d) {
      u = u + 3;
      c = c + 1;
  }
}
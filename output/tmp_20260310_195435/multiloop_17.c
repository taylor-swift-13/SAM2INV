int main1(){
  int u, s, h, anr, x;
  u=1*5;
  s=0;
  h=-1;
  anr=5;
  x=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant anr == h*h - 2*h + 2;
  loop invariant x == s*(h+2);
  loop invariant h <= u + 1;
  loop invariant x == s*(h + 1);
  loop assigns anr, x, h;
*/
while (h<=u) {
      anr = (anr+2*h)+(-(1));
      x = x + s;
      h += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant anr >= s;
  loop invariant anr >= 5;
  loop assigns anr;
*/
while (anr+1<=s) {
      anr = anr + 1;
  }
/*@
  assert !(anr+1<=s) &&
         (anr == h*h - 2*h + 2);
*/

}
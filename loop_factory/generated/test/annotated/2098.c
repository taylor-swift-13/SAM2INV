int main1(int y){
  int g, kdm, b2, b;
  g=y+4;
  kdm=0;
  b2=g;
  b=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b2 == y + 4 + kdm * y;
  loop invariant b == -2 - kdm * y;
  loop invariant b2 == (g + kdm * y);
  loop invariant kdm >= 0;
  loop invariant (g >= 0 ==> kdm <= g);
  loop assigns b2, kdm, b;
*/
while (kdm < g) {
      b2 = b2 + y;
      kdm++;
      b = (b)+(-(y));
  }
}
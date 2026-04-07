int main1(){
  int fi, d, g4, baz, j1f;
  fi=1;
  d=0;
  g4=1;
  baz=2;
  j1f=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= d && d <= fi);
  loop invariant baz == (2 + d * j1f);
  loop invariant g4 == (1 + d * 2 + j1f * ((d * (d - 1)) / 2));
  loop assigns g4, d, baz;
*/
while (d < fi) {
      g4 = g4 + baz;
      d++;
      baz = (j1f)+(baz);
  }
}
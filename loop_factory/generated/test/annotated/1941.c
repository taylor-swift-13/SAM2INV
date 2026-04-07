int main1(int v){
  int ay, g, w, mw;
  ay=v;
  g=v;
  w=v;
  mw=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ay == \at(v, Pre);
  loop invariant (g == w);
  loop invariant (w == mw);
  loop invariant g >= ay;
  loop invariant ay == v;
  loop assigns g, w, mw;
*/
while (g > ay) {
      w = w - 1;
      mw--;
      g -= 1;
  }
}
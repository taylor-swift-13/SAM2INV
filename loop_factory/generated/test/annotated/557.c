int main1(int r){
  int b4z, s, fn, hy, ytb;
  b4z=68;
  s=0;
  fn=r;
  hy=r;
  ytb=b4z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b4z == 68;
  loop invariant 0 <= s <= b4z;
  loop invariant (ytb - b4z) == (fn - \at(r, Pre));
  loop invariant ((ytb - b4z) == (hy - r) && (hy - r) == (fn - r));
  loop assigns ytb, hy, fn, s;
*/
while (s<b4z) {
      ytb += 1;
      hy = hy + 1;
      fn = (1)+(fn);
      s = b4z;
  }
}
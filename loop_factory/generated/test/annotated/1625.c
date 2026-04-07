int main1(int r){
  int o, ov2a, ka, eq1h, kw;
  o=10;
  ov2a=0;
  ka=ov2a;
  eq1h=r;
  kw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kw == r * ov2a;
  loop invariant ka == ov2a;
  loop invariant 0 <= ov2a;
  loop invariant ov2a <= o;
  loop invariant (eq1h == r + (kw * (ov2a + 1)) / 2);
  loop assigns ov2a, kw, ka, eq1h;
*/
while (1) {
      if (!(ov2a < o)) {
          break;
      }
      ov2a++;
      kw += r;
      eq1h += kw;
      ka = ka + 1;
  }
}
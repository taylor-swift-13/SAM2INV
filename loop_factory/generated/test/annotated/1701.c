int main1(){
  int t, zf, d1ju, wyn, g;
  t=58;
  zf=t;
  d1ju=t;
  wyn=0;
  g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d1ju == 58;
  loop invariant t == 58;
  loop invariant zf <= t;
  loop invariant (g == 0) || (g == 58);
  loop invariant wyn <= 0;
  loop invariant g <= d1ju;
  loop assigns d1ju, zf, g, wyn;
*/
while (1) {
      if (!(zf < t)) {
          break;
      }
      d1ju = (d1ju+g)+(-(g));
      zf += 1;
      g = g+d1ju-g;
      wyn = wyn+wyn-d1ju;
  }
}
int main1(int v){
  int g2t, f7;
  g2t=4;
  f7=g2t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f7 == 0 || f7 == 4;
  loop invariant v == \at(v, Pre) + ((4 - f7) / 4) * g2t;
  loop invariant g2t == 4;
  loop invariant 0 <= f7 <= 4;
  loop assigns f7, v;
*/
while (f7!=0&&f7!=0) {
      if (f7>f7) {
          f7 = f7 - f7;
      }
      else {
          f7 = f7 - f7;
      }
      v = v + g2t;
  }
}
int main1(int d){
  int x, a, g9og, wokz, fq;
  x=27;
  a=(d%60)+60;
  g9og=(d%9)+2;
  wokz=0;
  fq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == (\at(d, Pre) % 60) + 60;
  loop invariant g9og == (\at(d, Pre) % 9) + 2;
  loop invariant 0 <= wokz;
  loop invariant d == \at(d, Pre) + x * (wokz * g9og + fq);
  loop invariant d == \at(d, Pre) + 27*(wokz*g9og + fq);
  loop assigns fq, wokz, d;
*/
while (1) {
      if (!(a>g9og*wokz+fq)) {
          break;
      }
      if (fq==g9og-1) {
          fq = 0;
          wokz = wokz + 1;
      }
      else {
          fq += 1;
      }
      d += x;
  }
}
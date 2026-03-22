int main1(){
  int v, niqd, bjb, uj, aef, t3k, iiy, e;
  v=1;
  niqd=v;
  bjb=0;
  uj=0;
  aef=-3;
  t3k=5;
  iiy=-6;
  e=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= bjb <= v;
  loop invariant -3 <= aef;
  loop invariant 5 <= t3k;
  loop invariant -6 <= iiy;
  loop invariant 2*uj == bjb*(bjb-1);
  loop assigns uj, aef, bjb, t3k, iiy;
*/
while (1) {
      if (!(bjb<v)) {
          break;
      }
      uj += bjb;
      aef = aef + uj;
      bjb += 1;
      aef += 4;
      t3k += aef;
      iiy += t3k;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 1;
  loop invariant e >= 12;
  loop invariant aef >= -3;
  loop assigns aef, e, t3k, v;
*/
while (t3k<=niqd) {
      v = v+t3k*t3k;
      t3k++;
      e += v;
      aef = aef + 3;
  }
}
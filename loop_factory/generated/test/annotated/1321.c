int main1(int i){
  int ic, lmu3, ai, ds7, jw, m7lh;
  ic=i+23;
  lmu3=1;
  ai=0;
  ds7=1;
  jw=1;
  m7lh=lmu3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ic == i + 23;
  loop invariant ds7 == (ai + 1) * (ai + 1);
  loop invariant jw == 2 * ai + 1;
  loop invariant ai >= 0;
  loop invariant i == \at(i, Pre);
  loop invariant m7lh == (3 * ai * ai + 5 * ai + 2) / 2;
  loop assigns ai, ds7, jw, m7lh;
*/
while (ds7<=ic) {
      ai++;
      jw += 2;
      m7lh = m7lh+jw+ai;
      ds7 = ds7 + jw;
  }
}
int main1(int w){
  int b21, i, vj, r, vdu, v;
  b21=w;
  i=0;
  vj=31;
  r=0;
  vdu=1;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vdu == i + 1;
  loop invariant r <= b21 * (b21 + 1) / 2;
  loop invariant r <= i * (i + 1) / 2;
  loop invariant 0 <= vj;
  loop invariant 1 <= vdu;
  loop invariant r + vj == 31;
  loop invariant 0 <= v;
  loop invariant v <= vdu;
  loop invariant vj <= 31;
  loop assigns i, r, vj, vdu, v;
*/
while (vj>0&&i<b21) {
      if (vj<=vdu) {
          v = vj;
      }
      else {
          v = vdu;
      }
      i = i + 1;
      vj -= v;
      vdu += 1;
      r += v;
  }
}
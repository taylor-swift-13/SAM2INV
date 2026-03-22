int main1(int v){
  int p, r77, pnz, rrvi;
  p=26;
  r77=3;
  pnz=0;
  rrvi=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(v, Pre) + pnz * r77;
  loop invariant (rrvi == pnz) || (pnz == 0 && rrvi == v);
  loop invariant 0 <= pnz <= p;
  loop assigns rrvi, pnz, v;
*/
while (pnz<=p-1) {
      rrvi = pnz+1;
      pnz += 1;
      v += r77;
  }
}
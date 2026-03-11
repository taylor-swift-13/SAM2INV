int main1(int q){
  int iia, e9, v7gz, zbjt, gcv;
  iia=q+11;
  e9=iia;
  v7gz=0;
  zbjt=1;
  gcv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gcv == (e9 - (\at(q, Pre) + 11));
  loop invariant (v7gz * 3 + zbjt) == gcv + 1;
  loop invariant e9 <= (\at(q, Pre) + 11);
  loop invariant (e9 == iia - gcv);
  loop invariant (0 <= zbjt && zbjt <= 2);
  loop invariant (gcv >= 0);
  loop invariant gcv == e9 - iia;
  loop assigns gcv, zbjt, v7gz, e9;
*/
while (1) {
      if (!(e9<iia)) {
          break;
      }
      gcv += 1;
      zbjt++;
      if (zbjt>=3) {
          zbjt = zbjt - 3;
          v7gz += 1;
      }
      e9 += 1;
  }
}
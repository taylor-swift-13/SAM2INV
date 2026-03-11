int main1(int o){
  int ju9, zyj, zl8, r2;
  ju9=(o%13)+12;
  zyj=0;
  zl8=1;
  r2=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((r2 == 1) || (r2 == -1));
  loop invariant (1 <= zl8 && zl8 <= 10);
  loop invariant 0 <= zyj <= ju9;
  loop invariant ju9 == (\at(o, Pre) % 13) + 12;
  loop invariant ju9 == (o % 13) + 12;
  loop invariant ((zl8 + zyj) % 2) == 1;
  loop assigns r2, zyj, zl8;
*/
while (zyj<ju9) {
      if (zl8>=10) {
          r2 = -1;
      }
      if (zl8<=1) {
          r2 = 1;
      }
      zyj++;
      zl8 += r2;
  }
}
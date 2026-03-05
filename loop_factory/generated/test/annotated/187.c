int main1(){
  int zny, i18, x, nn;
  zny=1+13;
  i18=1;
  x=i18;
  nn=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i18 == 1;
  loop invariant zny == 14;
  loop invariant nn >= -1;
  loop invariant x == nn*nn + i18 || (nn == -1 && x == 1 && i18 == 1);
  loop assigns nn, x;
*/
while (i18<zny) {
      nn++;
      x = nn*nn;
      x += i18;
  }
}
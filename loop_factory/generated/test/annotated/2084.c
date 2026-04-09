int main1(){
  int j, cj, l, wbh;
  j=1;
  cj=0;
  l=8;
  wbh=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 1;
  loop invariant wbh == -3 - (cj * (cj - 1)) / 2;
  loop invariant l == 8 + (cj * (-3)) - (cj * (cj - 1) * (cj - 2)) / 6;
  loop invariant 0 <= cj <= j;
  loop assigns cj, l, wbh;
*/
while (1) {
      if (!(cj < j)) {
          break;
      }
      cj++;
      l = l + wbh;
      wbh = wbh+j-cj;
  }
}
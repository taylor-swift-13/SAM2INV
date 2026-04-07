int main1(){
  int r, wyu, sf9, l, whd;
  r=(1%18)+16;
  wyu=0;
  sf9=r;
  l=wyu;
  whd=r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= wyu;
  loop invariant wyu <= r;
  loop invariant whd == r;
  loop invariant 0 <= l;
  loop invariant sf9 == whd;
  loop invariant l <= r;
  loop assigns sf9, wyu, l;
*/
while (1) {
      if (!(wyu < r)) {
          break;
      }
      sf9 = (sf9+whd)/2;
      wyu = wyu + 1;
      l = (l+sf9)/2;
  }
}
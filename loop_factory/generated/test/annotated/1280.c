int main1(int j){
  int i5s, e, v0, v, yf, aaf;
  i5s=j*2;
  e=0;
  v0=0;
  v=0;
  yf=0;
  aaf=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aaf == 7 + 10*(e/5) + ((e%5)*((e%5)-1))/2;
  loop invariant v0 == aaf - 7;
  loop invariant i5s == 2 * j;
  loop invariant 7 <= aaf;
  loop invariant 0 <= e;
  loop invariant 0 <= v;
  loop invariant v <= 4;
  loop assigns v, yf, v0, e, aaf;
*/
while (e<i5s) {
      v = e%5;
      if (!(!(e>=aaf))) {
          yf = (e-aaf)%5;
          v0 = v0+v-yf;
      }
      else {
          v0 += v;
      }
      e += 1;
      aaf += v;
  }
}
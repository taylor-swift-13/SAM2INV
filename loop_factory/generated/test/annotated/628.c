int main1(){
  int l, n, s, wo;
  l=13;
  n=l;
  s=3;
  wo=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n <= l;
  loop invariant 3 <= s <= 12;
  loop invariant (wo == 1) || (wo == -1);
  loop invariant n - s >= 10;
  loop invariant l == 13;
  loop assigns n, s, wo;
*/
while (n<l) {
      if (s>=12) {
          wo = -1;
      }
      if (s<=3) {
          wo = 1;
      }
      s += wo;
      n += 1;
  }
}
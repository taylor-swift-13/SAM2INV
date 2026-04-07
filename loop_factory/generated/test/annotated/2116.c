int main1(int a){
  int a7, q, wj, fh, f;
  a7=a+21;
  q=0;
  wj=1;
  fh=0;
  f=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (wj + fh == 1);
  loop invariant (q == 0 || q == a7);
  loop invariant (f == -3 || (1 <= f && f <= a7));
  loop invariant a7 == \at(a, Pre) + 21;
  loop invariant ((q == 0 && f == -3) || (q == a7 && f == 1));
  loop invariant a7 == a + 21;
  loop invariant (q >= 0) && (q == 0 || q <= a7);
  loop assigns f, wj, fh, q;
*/
while (q < a7) {
      f = (wj += (q < a7/2 ? a : -a), fh -= (q < a7/2 ? a : -a), ++q);
      wj = wj+f-f;
      q = a7;
  }
}
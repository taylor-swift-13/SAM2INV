int main1(){
  int kp, n, pl;
  kp=0;
  n=(1%28)+10;
  pl=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 11 - (kp*(kp-1))/2;
  loop invariant pl == 13 + 11*kp - (kp*(kp+1)*(kp-1))/6;
  loop invariant pl >= 13;
  loop invariant 0 <= kp;
  loop invariant 1 <= n;
  loop assigns kp, n, pl;
*/
while (n>kp) {
      n = n - kp;
      kp = kp + 1;
      pl += n;
  }
}
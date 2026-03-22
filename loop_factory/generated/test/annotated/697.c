int main1(){
  int v, n, pze, yul, k5b, u7o;
  v=1+5;
  n=v;
  pze=0;
  yul=0;
  k5b=0;
  u7o=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k5b == yul;
  loop invariant pze == k5b * (n + 1);
  loop invariant k5b >= 0;
  loop invariant pze >= 0;
  loop invariant k5b + u7o == n;
  loop invariant u7o + k5b == (1%18) + 5;
  loop assigns k5b, pze, u7o, yul;
*/
while (u7o>0) {
      k5b = k5b+1*1;
      pze = pze+1*1;
      u7o -= 1;
      yul = yul+1*1;
      pze += n;
  }
}
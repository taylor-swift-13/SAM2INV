int main1(int l){
  int k6e, un, is;
  k6e=40;
  un=k6e;
  is=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant is == 822 - (un*(un+1))/2;
  loop invariant un <= k6e;
  loop invariant 0 <= un <= 40;
  loop assigns is, un;
*/
while (un-1>=0) {
      is = is + un;
      un = un - 1;
  }
}
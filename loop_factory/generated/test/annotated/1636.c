int main1(int x){
  int k4ko, kzow, egq;
  k4ko=x+8;
  kzow=-3;
  egq=k4ko;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k4ko == \at(x, Pre) + 8;
  loop invariant x == \at(x, Pre) + k4ko * (kzow + 3);
  loop invariant kzow >= -3;
  loop assigns egq, kzow, x;
*/
while (1) {
      if (!(kzow<=k4ko-1)) {
          break;
      }
      egq = k4ko-kzow;
      kzow = kzow + 1;
      x = x + k4ko;
  }
}
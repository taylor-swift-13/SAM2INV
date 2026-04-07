int main1(int j){
  int k, krf, pb2;
  k=(j%10)+14;
  krf=0;
  pb2=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == (\at(j, Pre) % 10) + 14;
  loop invariant 0 <= krf;
  loop invariant krf <= k;
  loop invariant (\at(j, Pre) >= 0 ==> pb2 >= \at(j, Pre)) && (\at(j, Pre) <= 0 ==> pb2 <= \at(j, Pre));
  loop invariant j == \at(j, Pre);
  loop assigns j, pb2, krf;
*/
while (j-- > 0) {
      pb2 += pb2;
      krf = (krf + 1 > k) ? (2*k - (krf + 1)) : ((krf - 1 < 0) ? -(krf - 1) : (krf + 1));
      j++;
  }
}
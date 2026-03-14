int main1(int k,int x){
  int rxs, pa4, m, du;
  rxs=k;
  pa4=3;
  m=0;
  du=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rxs == \at(k,Pre);
  loop invariant 0 <= m;
  loop invariant (m == 0 ==> du == -5);
  loop invariant (m > 0 ==> du == rxs - (m - 1));
  loop invariant k == \at(k, Pre) + pa4 * m;
  loop invariant pa4 == 3;
  loop assigns du, m, k;
*/
while (m<rxs) {
      du = (rxs)+(-(m));
      m++;
      k = k + pa4;
  }
}
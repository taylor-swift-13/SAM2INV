int main1(int d,int s){
  int qn, q;
  qn=4;
  q=qn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q <= qn;
  loop invariant q >= 0;
  loop invariant d == \at(d, Pre);
  loop invariant q == 0 || q == qn;
  loop invariant qn == 4;
  loop invariant s >= \at(s, Pre);
  loop invariant (s - \at(s, Pre)) % 2 == 0;
  loop assigns d, q, s;
*/
while (q!=0&&q!=0) {
      if (q>q) {
          q = q - q;
      }
      else {
          q = q - q;
      }
      d = d + q;
      s += 2;
  }
}
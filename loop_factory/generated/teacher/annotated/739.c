int main1(int b,int k,int p,int q){
  int l, c, m;

  l=k-5;
  c=0;
  m=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 0;
  loop invariant m == 8 || m == 0;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant l == k - 5;
  loop invariant m >= 0;
  loop invariant m <= 8;
  loop invariant (m == 8) || (m == 0);
  loop assigns m;
*/
while (1) {
      m = m+2;
      if ((c%7)==0) {
          m = m+c;
      }
      m = m-m;
  }

}

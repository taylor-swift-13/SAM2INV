int main1(int l){
  int n, ca, gt, ocqb, df, m, n7oh, q;
  n=l+23;
  ca=-6;
  gt=1;
  ocqb=ca;
  df=0;
  m=ca;
  n7oh=ca;
  q=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ocqb >= ca;
  loop invariant ca == -6;
  loop invariant q >= \at(l, Pre);
  loop invariant m == 2 * n7oh - ca;
  loop invariant gt == 1;
  loop invariant df == 0;
  loop invariant n7oh == 2*ocqb + 6;
  loop invariant (n != ca) ==> (q == l);
  loop invariant n == ca || n == \at(l, Pre) + 23;
  loop assigns l, q, gt, ocqb, df, m, n7oh, n;
*/
while (ca+1<=n) {
      if (ca%4==3) {
          gt = gt + 1;
      }
      else {
          ocqb++;
      }
      if (ca%4==0) {
          df++;
      }
      else {
      }
      m = (4)+(m);
      n7oh += 2;
      q = q + gt;
      l = (l+gt)%4;
      n = (ca+1)-1;
  }
}
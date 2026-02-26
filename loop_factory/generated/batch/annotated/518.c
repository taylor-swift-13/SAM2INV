int main1(int k,int q){
  int h, c, v, n;

  h=k-2;
  c=0;
  v=c;
  n=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 2*c;
  loop invariant h == k - 2;
  loop invariant c >= 0;
  loop invariant v >= 0;
  loop invariant c <= h || h < 0;
  loop invariant 0 <= c;
  loop invariant (c <= h) || (h <= 0);
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns v, c;
*/
while (1) {
      if (c>=h) {
          break;
      }
      v = v+2;
      c = c+1;
  }

}

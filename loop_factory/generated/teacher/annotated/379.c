int main1(int p,int q){
  int e, s, k, t;

  e=q+11;
  s=3;
  k=p;
  t=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant e == \at(q, Pre) + 11;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t >= 0;
  loop invariant e == q + 11;

  loop invariant ((\at(p, Pre) >= 0) ==> k >= 0) && ((\at(p, Pre) < 0) ==> k <= 0) && t >= 0;
  loop assigns k, t;
*/
while (k!=0&&t!=0) {
      if (k>t) {
          k = k-t;
      }
      else {
          t = t-k;
      }
  }

}

int main1(int p,int q){
  int o, k, h, u;

  o=q+6;
  k=0;
  h=8;
  u=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 8 + 2*u*k;
  loop invariant u == \at(q, Pre);
  loop invariant o == \at(q, Pre) + 6;

  loop invariant k >= 0;
  loop invariant o == q + 6;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant q == \at(q, Pre) && 0 <= k && (o >= 0 ==> k <= o);
  loop assigns h, k;
*/
while (k<o) {
      h = h+u+u;
      k = k+1;
  }

}

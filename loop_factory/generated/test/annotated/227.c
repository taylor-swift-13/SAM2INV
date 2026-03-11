int main1(){
  int q, b, kfn, p2, xmn, t;
  q=1-4;
  b=q+5;
  kfn=3;
  p2=0;
  xmn=4;
  t=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t - b * p2 == b;
  loop invariant p2 >= 0;
  loop invariant 2 * xmn == p2 * p2 + 7 * p2 + 8;
  loop invariant p2 == kfn - 3;
  loop invariant t == 2 + 2*p2;
  loop invariant t == 2 + b * p2;
  loop assigns kfn, p2, xmn, t;
*/
while (1) {
      if (!(p2<=q-1)) {
          break;
      }
      kfn++;
      p2 = p2 + 1;
      xmn = xmn + kfn;
      t += b;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p2 >= 0;
  loop invariant kfn >= 3;
  loop invariant xmn >= 4;
  loop assigns p2, xmn;
*/
while (xmn<kfn) {
      p2 = p2 + 1;
      xmn = xmn + 1;
      if ((t%8)==0) {
          p2 = p2*2;
      }
  }
}
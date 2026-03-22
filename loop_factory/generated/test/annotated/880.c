int main1(int e){
  int hk, clv, q;
  hk=(e%14)+13;
  clv=0;
  q=hk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hk == (\at(e, Pre) % 14) + 13;
  loop invariant e == \at(e, Pre);
  loop invariant (clv == 0) || (clv == hk);
  loop invariant q >= hk;
  loop invariant q <= hk + 1;
  loop invariant ((clv == 0) ==> (q == hk));
  loop assigns q, e, clv;
*/
while (1) {
      if (!(clv<hk)) {
          break;
      }
      q += 1;
      e = e + clv;
      clv = hk;
  }
}
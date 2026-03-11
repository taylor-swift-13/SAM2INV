int main1(int l){
  int qr, yxvi, w, lt, lnx, af;
  qr=(l%31)+15;
  yxvi=-6;
  w=5;
  lt=0;
  lnx=l;
  af=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant af == 3 + lt*lt + lt*(yxvi + l + 1);
  loop invariant lnx == l + 2*lt;
  loop invariant w == 5 + lt * l;
  loop invariant 0 <= lt;
  loop invariant (qr >= 0) ==> lt <= qr;
  loop invariant qr == (\at(l, Pre) % 31) + 15;
  loop invariant yxvi == -6;
  loop invariant l == \at(l, Pre);
  loop invariant 0 <= lt && (lt == 0 || lt <= qr);
  loop assigns af, w, lnx, lt;
*/
while (lt<=qr-1) {
      af += yxvi;
      w += l;
      lt += 1;
      lnx += 2;
      af += lnx;
  }
/*@
  assert (l == \at(l, Pre)) &&
         (qr == (\at(l, Pre) % 31) + 15) &&
         (lnx == l + 2 * lt) &&
         (w == 5 + lt * l) &&
         (af == 3 + lt * lt + lt * (l - 5)) &&
         ((qr <= 0 ==> lt == 0)) &&
         ((qr > 0 ==> lt == qr));
*/
}

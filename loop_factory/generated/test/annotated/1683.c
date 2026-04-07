int main1(int q){
  int a, vq, fa, u0bu, oci;
  a=(q%37)+13;
  vq=0;
  fa=q;
  u0bu=q;
  oci=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fa == \at(q,Pre);
  loop invariant a == (\at(q,Pre) % 37) + 13;
  loop invariant 0 <= vq;
  loop invariant (vq == 0) ==> (q == \at(q, Pre));
  loop invariant u0bu == \at(q, Pre);
  loop invariant oci == 8;
  loop invariant (vq > 0) ==> (q - fa - u0bu == oci);
  loop assigns fa, vq, q;
*/
while (vq < a) {
      fa = fa+oci-oci;
      vq = vq + 1;
      q = fa+u0bu+oci;
  }
}
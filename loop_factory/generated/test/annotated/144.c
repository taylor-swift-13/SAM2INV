int main1(int b){
  int sf, xz, k, gly, u17, vms, qzy;
  sf=(b%14)+17;
  xz=3;
  k=3;
  gly=3;
  u17=0;
  vms=8;
  qzy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qzy == xz - 3;
  loop invariant 3 <= xz;
  loop invariant xz <= sf;
  loop invariant 0 <= k;
  loop invariant k <= vms;
  loop invariant u17 + gly - 3 <= qzy;
  loop invariant b == \at(b, Pre);
  loop invariant vms == 8 + ((xz - 3) / 2);
  loop invariant gly >= 3;
  loop invariant u17 <= qzy;
  loop invariant sf == (\at(b, Pre) % 14) + 17;
  loop invariant 0 <= u17;
  loop invariant gly <= 3 + qzy;
  loop invariant k + u17 == gly;
  loop assigns k, u17, gly, qzy, xz, vms;
*/
while (xz<sf) {
      if (xz%3==0) {
          if (k>0) {
              k = k - 1;
              u17 += 1;
          }
      }
      else {
          if (k<vms) {
              k += 1;
              gly += 1;
          }
      }
      qzy += 1;
      xz += 1;
      vms = vms+(xz%2);
  }
}
int main1(int r,int u){
  int ptp, v0z, vr, hv2p, l71;
  ptp=r+19;
  v0z=0;
  vr=0;
  hv2p=0;
  l71=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hv2p == vr*(11 - vr)/2;
  loop invariant u == \at(u, Pre) + vr*(ptp - v0z);
  loop invariant 0 <= vr <= 5;
  loop invariant l71 == 5 - vr;
  loop invariant ptp == r + 19;
  loop assigns hv2p, vr, l71, u;
*/
while (vr<ptp&&l71>0) {
      hv2p += l71;
      vr++;
      l71 = l71 - 1;
      u = u+ptp-v0z;
  }
}
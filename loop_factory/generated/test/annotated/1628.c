int main1(int g){
  int mh, zj, fp, xrp;
  mh=g;
  zj=0;
  fp=12;
  xrp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zj >= 0;
  loop invariant fp == 12 + zj;
  loop invariant xrp == -zj;
  loop invariant g == \at(g, Pre) + 12*zj + zj*(zj+1)/2;
  loop invariant mh == \at(g, Pre);
  loop assigns xrp, zj, fp, g;
*/
while (zj < mh) {
      xrp -= 1;
      zj = zj + 1;
      fp++;
      g += fp;
  }
}
int main1(int k,int v){
  int fp, rz, zsg;
  fp=26;
  rz=0;
  zsg=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (rz==0 && zsg==1) || (rz>0 && (zsg==2 || zsg==4 || zsg==8));
  loop invariant fp == 26;
  loop invariant v == \at(v, Pre);
  loop invariant k - \at(k, Pre) >= 2 * rz;
  loop invariant k - \at(k, Pre) <= 8 * rz;
  loop invariant 0 <= rz <= fp;
  loop invariant (k - \at(k,Pre)) % 2 == 0;
  loop assigns zsg, rz, k;
*/
while (rz<fp) {
      if (zsg>=7) {
          zsg = -1;
      }
      if (zsg<=1) {
          zsg = 1;
      }
      zsg += zsg;
      rz += 1;
      k += zsg;
  }
}
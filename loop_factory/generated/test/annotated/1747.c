int main1(){
  int qjh, dlua, ha, gy, zx;
  qjh=1+8;
  dlua=0;
  ha=qjh;
  gy=qjh;
  zx=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= dlua <= qjh;
  loop invariant gy == ha;
  loop invariant 0 <= zx;
  loop invariant zx <= 2;
  loop assigns dlua, zx, gy, ha;
*/
while (dlua < qjh) {
      dlua += 1;
      zx = dlua % 3;
      gy += zx;
      ha += zx;
  }
}
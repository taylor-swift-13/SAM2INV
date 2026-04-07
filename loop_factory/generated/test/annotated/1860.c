int main1(){
  int z, b32, i, vpj, r, h9, qc, k5m, w;
  z=110;
  b32=0;
  i=b32;
  vpj=z;
  r=b32;
  h9=b32;
  qc=z;
  k5m=z;
  w=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (z == b32 + 6) || (b32 == 0 && z == 110);
  loop invariant i >= 0;
  loop invariant vpj >= 0;
  loop invariant r >= 0;
  loop invariant h9 >= 0;
  loop invariant qc >= 0;
  loop invariant w >= 0;
  loop invariant b32 == 0;
  loop invariant z >= b32 + 6;
  loop invariant k5m >= h9;
  loop invariant qc >= 110;
  loop invariant w >= 110;
  loop invariant z <= 110;
  loop invariant k5m >= 110;
  loop invariant (i + vpj) >= 110;
  loop invariant (b32 == 0) && (vpj == 110) && (r == 0) && (w == 110);
  loop invariant (z >= b32 + 6);
  loop invariant k5m - h9 >= 110;
  loop invariant b32 == 0 && i >= 0 && vpj >= 110 && r == 0 && h9 >= 0 && qc >= 110 && w >= 110 && z <= 110 && k5m >= 110;
  loop invariant h9 == i*(i+1)/2;
  loop invariant w == 110;
  loop assigns i, vpj, r, qc, h9, w, k5m, z;
*/
while (b32+7<=z) {
      if (b32%6==0) {
          i = i + 1;
      }
      else {
          vpj = vpj + 1;
      }
      if (b32%6==1) {
          r = r + 1;
      }
      else {
      }
      qc = qc + k5m;
      h9 = h9 + i;
      w = w + b32;
      k5m = (h9)+(k5m);
      z = (b32+7)-1;
  }
}
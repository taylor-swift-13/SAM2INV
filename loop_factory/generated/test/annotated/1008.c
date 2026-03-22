int main1(int z,int q){
  int bgy5, mvk1, y8, zzm;
  bgy5=192;
  mvk1=0;
  y8=0;
  zzm=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bgy5 == 192;
  loop invariant zzm == 1 || zzm == -1;
  loop invariant q == \at(q, Pre);
  loop invariant z == \at(z, Pre);
  loop invariant 0 <= mvk1 <= bgy5;
  loop invariant 0 <= y8 <= 10;
  loop invariant y8 <= mvk1;
  loop invariant (mvk1 - y8) % 2 == 0;
  loop assigns y8, mvk1, zzm;
*/
while (mvk1<bgy5) {
      if (y8>=10) {
          zzm = -1;
      }
      if (!(y8>0)) {
          zzm = 1;
      }
      y8 = y8 + zzm;
      mvk1 += 1;
  }
}
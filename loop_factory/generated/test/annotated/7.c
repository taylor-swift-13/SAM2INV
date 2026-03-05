int main1(int k,int z){
  int zf;
  zf=15;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zf == 15;
  loop invariant k == \at(k, Pre);
  loop invariant z == \at(z, Pre);
  loop assigns zf;
*/
while (zf>0) {
      zf += 1;
      zf = zf - 1;
  }
}
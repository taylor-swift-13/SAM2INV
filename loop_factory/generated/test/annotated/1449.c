int main1(int z){
  int jcm, bs, wi8, xv;
  jcm=z;
  bs=0;
  wi8=0;
  xv=bs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(z, Pre) + wi8 * jcm;
  loop invariant (wi8 <= jcm/2) ==> (xv == 0);
  loop invariant z == \at(z, Pre) * (wi8 + 1);
  loop invariant 0 <= wi8;
  loop assigns z, wi8, xv;
*/
while (wi8<jcm) {
      if (!(!(wi8>=jcm/2))) {
          xv += 2;
      }
      z += jcm;
      wi8++;
  }
}
int main1(){
  int x0t, oh, z3, zza, mb;
  x0t=3;
  oh=(1%20)+1;
  z3=(1%25)+1;
  zza=0;
  mb=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= z3;
  loop invariant z3 <= 2;
  loop invariant zza >= 0;
  loop invariant mb >= 6;
  loop invariant oh >= 2;
  loop invariant zza <= 4;
  loop invariant ((z3 == 2 && mb == 6 && oh == 2 && zza == 0) ||
                    (z3 == 1 && mb == 10 && oh == 4 && zza == 0) ||
                    (z3 == 0 && mb == 13 && oh == 8 && zza == 4));
  loop assigns zza, z3, oh, mb;
*/
while (z3!=0) {
      if (z3%2==1) {
          zza = zza + oh;
          z3 = z3 - 1;
      }
      else {
      }
      oh = 2*oh;
      z3 = z3/2;
      mb = mb + z3;
      mb += x0t;
  }
}
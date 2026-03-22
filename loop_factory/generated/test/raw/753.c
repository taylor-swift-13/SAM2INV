int main1(){
  int x0t, oh, z3, zza, mb;

  x0t=3;
  oh=(1%20)+1;
  z3=(1%25)+1;
  zza=0;
  mb=6;

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

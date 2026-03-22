int main1(){
  int smk, zf, jpl, owp, d2;

  smk=27;
  zf=smk+6;
  jpl=(1%40)+2;
  owp=0;
  d2=zf;

  while (1) {
      if (!(jpl!=owp)) {
          break;
      }
      owp = jpl;
      d2 += owp;
      jpl = (jpl+smk/jpl)/2;
      d2 = d2*3;
  }

}

int main1(){
  int aud2, dbfp, ef, r;

  aud2=1+18;
  dbfp=0;
  ef=aud2;
  r=aud2;

  while (ef >= (2*dbfp + 1)) {
      ef = (ef)+(-((2*dbfp + 1)));
      r += aud2;
      dbfp++;
  }

}

int main1(){
  int i5, dg, s, b2at, cjq, erx;

  i5=1;
  dg=i5;
  s=25;
  b2at=0;
  cjq=(1%6)+2;
  erx=5;

  while (1) {
      if (b2at>=i5) {
          break;
      }
      dg = dg*cjq+1;
      s = s*cjq;
      b2at++;
      cjq = cjq + dg;
      erx = erx*2+(s%2)+1;
      cjq = cjq + erx;
  }

}

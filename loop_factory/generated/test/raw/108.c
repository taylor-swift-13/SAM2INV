int main1(){
  int bk, p56, msv;

  bk=1+15;
  p56=4;
  msv=2;

  while (p56<=bk-1) {
      if (msv==1) {
          msv = 2;
      }
      else {
          if (msv==2) {
              msv = 1;
          }
      }
      msv = msv + 1;
      msv -= msv;
  }

}

int main1(int y){
  int n1hk, yn, sukq, e, dnr;

  n1hk=39;
  yn=0;
  sukq=0;
  e=0;
  dnr=0;

  while (1) {
      if (!(yn<n1hk)) {
          break;
      }
      e += 1;
      dnr = dnr + 1;
      if (e>=2) {
          e -= 2;
          sukq += 1;
      }
      yn = yn + 1;
  }

}

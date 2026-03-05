int main1(){
  int rc, a, dj, az;

  rc=65;
  a=0;
  dj=2;
  az=1;

  while (a<rc) {
      if (dj>=9) {
          az = -1;
      }
      if (dj<=2) {
          az = 1;
      }
      dj = dj + az;
      a++;
      dj = dj + 3;
  }

}

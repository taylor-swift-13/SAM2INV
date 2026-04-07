int main1(){
  int r1d, hz, c;

  r1d=60;
  hz=0;
  c=2;

  while (hz+1<=r1d) {
      if (c==1) {
          c = 2;
      }
      else {
          if (c==2) {
              c = 1;
          }
      }
      r1d = (hz+1)-1;
  }

}

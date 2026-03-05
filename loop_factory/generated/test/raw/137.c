int main1(){
  int e, kc, i;

  e=(1%33)+6;
  kc=1;
  i=0;

  while (kc<e) {
      if (kc%2==0) {
          if (i>0) {
              i--;
              i = i + 1;
          }
      }
      else {
          if (i>0) {
              i--;
              i = i + 1;
          }
      }
      kc += 1;
      i = i + 5;
  }

}

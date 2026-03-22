int main1(){
  int b3gd, fotd, a, cgq3, kw2, kb, mu;

  b3gd=1*3;
  fotd=1;
  a=0;
  cgq3=0;
  kw2=0;
  kb=3;
  mu=0;

  while (fotd<b3gd) {
      if (fotd%3==0) {
          if (a>0) {
              a -= 1;
              kw2 = kw2 + 1;
          }
      }
      else {
          if (a<kb) {
              a++;
              cgq3 = cgq3 + 1;
          }
      }
      mu++;
      fotd = fotd + 1;
  }

}

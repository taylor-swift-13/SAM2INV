int main1(){
  int tz, uj, jsi, vb, jme, uto;

  tz=1;
  uj=0;
  jsi=0;
  vb=0;
  jme=0;
  uto=0;

  while (uj<tz) {
      if (!(!(uj%8==0))) {
          if (uj%5==0) {
              jme++;
          }
          else {
              if (uj%3==0) {
                  vb = vb + 1;
              }
              else {
                  jsi += 1;
              }
          }
      }
      else {
          uto += 1;
      }
      uj++;
      jsi += 1;
  }

}

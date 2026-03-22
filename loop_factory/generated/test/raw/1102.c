int main1(int v,int e){
  int vs9, jkfm, nnr, hi, ue5, ftm;

  vs9=e-7;
  jkfm=0;
  nnr=0;
  hi=0;
  ue5=0;
  ftm=0;

  while (1) {
      if (!(jkfm<vs9)) {
          break;
      }
      if (!(!(jkfm%11==0))) {
          if (jkfm%9==0) {
              ue5++;
          }
          else {
              if (jkfm%4==0) {
                  hi += 1;
              }
              else {
                  nnr++;
              }
          }
      }
      else {
          ftm = ftm + 1;
      }
      jkfm++;
      v = v + ue5;
  }

  while (1) {
      ue5++;
      if (ue5>=jkfm) {
          break;
      }
  }

}

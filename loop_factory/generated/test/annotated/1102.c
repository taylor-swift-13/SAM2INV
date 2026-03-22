int main1(int v,int e){
  int vs9, jkfm, nnr, hi, ue5, ftm;
  vs9=e-7;
  jkfm=0;
  nnr=0;
  hi=0;
  ue5=0;
  ftm=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ue5;
  loop invariant 0 <= hi;
  loop invariant 0 <= nnr;
  loop invariant 0 <= ftm;
  loop invariant jkfm == ftm + ue5 + hi + nnr;
  loop invariant v >= \at(v,Pre);
  loop invariant vs9 == \at(e, Pre) - 7;
  loop assigns ue5, hi, nnr, ftm, jkfm, v;
*/
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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ue5;
  loop invariant 0 <= jkfm;
  loop invariant ue5 <= jkfm;
  loop invariant v >= \at(v,Pre);
  loop assigns ue5;
*/
while (1) {
      ue5++;
      if (ue5>=jkfm) {
          break;
      }
  }
}